import KnightModel.Transfinite.SuccessorRank
import KnightModel.Transfinite.SuccessorOrder
import KnightModel.RankTwo.RestrictionCardinal

/-! # The upper spectrum of the successor directly from its old sort

A model of the successor sentence interprets a model of the old sentence.
Over a fixed point and all old elements, the points definable over some finite
tuple have cardinal at most the maximum of the size of the old sort and ℵ₀.
The source frame-support calculation makes these sets cover each pair.
-/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott Set Cardinal

namespace SuccessorBound

variable (P : Seed) {N : Type} (E : Scott.Model (SuccessorRelation P.R) N)

abbrev Old := {x : N // E (.base .indexSort) (fun _ => x)}

def oldModel : Scott.Model P.R (Old P E) :=
  fun r t => E (.base (.old r)) (Subtype.val ∘ t)

local notation "D" => smallModel P.D P.mark
local notation "ι" => SuccessorAut.indexIn P

private theorem comp_push {X Y : Type} (f : X → Y) {n} (x : X) (s : Tuple X n) :
    f ∘ push x s = push (f x) (f ∘ s) := funext (Fin.cases rfl (fun _ => rfl))

variable {E}

def project (F : BackAndForth (D) E) : BackAndForth P.D (oldModel P E) where
  matchTuples := fun s t => F.matchTuples (ι ∘ s) (Subtype.val ∘ t)
  atoms := by
    intro n s t h a
    cases a with
    | eq j k =>
      have hh := F.atoms h (.eq j k)
      exact ⟨fun e => Subtype.ext (hh.mp (congrArg (ι) e)),
        fun e => (SuccessorAut.indexSort P).injective (hh.mpr (congrArg Subtype.val e))⟩
    | rel r v =>
      exact (SuccessorAut.oldModel_iff P r (s ∘ v)).symm.trans (F.atoms h (.rel (.base (.old r)) v))
  forth := by
    intro n s t h x
    obtain ⟨y,hy⟩ := F.forth h (ι x)
    have tagged := (SuccessorAut.indexPred P _).mpr ⟨x,rfl⟩
    have mem := (F.atoms hy (.rel (.base .indexSort) (fun _ => 0))).mp tagged
    exact ⟨⟨y,mem⟩,by rwa [comp_push, comp_push]⟩
  back := by
    intro n s t h y
    obtain ⟨x,hx⟩ := F.back h y.val
    have tagged := (F.atoms hx (.rel (.base .indexSort) (fun _ => 0))).mpr y.property
    obtain ⟨a,rfl⟩ := (SuccessorAut.indexPred P x).mp tagged
    exact ⟨a,by rwa [comp_push, comp_push]⟩

private theorem extend_pair (F : BackAndForth (D) E) {a b : SmallCarrier P.mark} {x y : N}
    (start : F.Lifts (push a (push b (n := 0) Fin.elim0)) (push x (push y Fin.elim0)))
    {n : ℕ} (u : Tuple P.M n) :
    ∃ v : Tuple (Old P E) n, F.Lifts (push a (push b (ι ∘ u)))
      (push x (push y (Subtype.val ∘ v))) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_⟩
    simpa only [Subsingleton.elim (ι ∘ u) Fin.elim0,
      Subsingleton.elim (Subtype.val ∘ (Fin.elim0 : Fin 0 → Old P E)) Fin.elim0] using start
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih (Fin.tail u)
    obtain ⟨z,hz⟩ := F.closure.forth ht (ι (u 0))
    have tagged := (SuccessorAut.indexPred P _).mpr ⟨u 0,rfl⟩
    have mem := (F.closure.atoms hz (.rel (.base .indexSort) (fun _ => 0))).mp tagged
    let z' : Old P E := ⟨z,mem⟩
    let p : Fin (n+3) → Fin (n+3) := Fin.cases 1 (Fin.cases 2
      (Fin.cases 0 (fun j => j.succ.succ.succ)))
    refine ⟨push z' t,?_⟩
    have hh := hz.select F p
    convert hh using 1 <;> funext j <;>
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) j

private theorem pair_lifts {x y : N} (F : BackAndForth (D) E)
    {a b : SmallCarrier P.mark}
    (start : F.Lifts (push a (push b (n := 0) Fin.elim0)) (push x (push y Fin.elim0)))
    (s : List P.M) (rank : ModelRankLE (D) 0 (b :: s.map (ι)) a) :
    ∃ v : Sigma (Tuple (Old P E)), x ∈ lowFiber F 0 (push y (Subtype.val ∘ v.2)) := by
  obtain ⟨t,ht⟩ := extend_pair P F start s.get
  refine ⟨⟨s.length,t⟩,a,push b (ι ∘ s.get),?_,ht⟩
  rw [ofFn_push]
  have he : List.ofFn (ι ∘ s.get) = s.map (ι) := by rw [← List.map_ofFn, List.ofFn_get]
  rwa [he]

/-- The successor Scott bound follows from the preceding spectrum alone. -/
theorem bound {κ : Cardinal.{0}} (inf : ℵ₀ ≤ κ) (old : P.Bounded κ)
    (C : Presentation (SuccessorRelation P.R) (SmallCarrier P.mark))
    (sat : BackAndForth.Satisfies E (C.sentence (D))) : #N ≤ Order.succ κ := by
  obtain ⟨F,empty⟩ := (C.satisfies_iff_backAndForth _ _).mp sat
  have oldSize : #(Old P E) ≤ κ := by
    apply old (oldModel P E)
    apply (P.pres.satisfies_iff_backAndForth ..).mpr
    refine ⟨project P F,?_⟩
    change F.matchTuples _ _
    convert empty using 1
  let T := Sigma (Tuple (Old P E))
  let L (y : N) (v : T) := lowFiber F 0 (push y (Subtype.val ∘ v.2))
  apply cardinal_le_succ_of_pair_cover inf (fun y => ⋃ v, L y v)
  · intro y
    have sizeT : #T ≤ κ := by
      calc #T = #(List (Old P E)) := mk_congr (List.equivSigmaTuple (α := Old P E)).symm
           _ ≤ κ := (mk_list_le_max _).trans (max_le inf oldSize)
    calc
      #(⋃ v, L y v) ≤ #T * ⨆ v, #(L y v) := mk_iUnion_le _
      _ ≤ κ * κ := mul_le_mul' sizeT (ciSup_le' fun v => by
        apply LE.le.trans _ inf
        simpa only [Nat.cast_zero,aleph_zero] using
          lowFiber_cardinal F C 0 (push y (Subtype.val ∘ v.2)))
      _ = κ := mul_eq_self inf
  · intro x y
    obtain ⟨b,hb⟩ := F.back empty y
    obtain ⟨a,ha⟩ := F.back hb x
    have hh := F.lifts_of_match ha
    rcases SuccessorAut.pair_dependence P a b with ⟨s,hs⟩ | ⟨s,hs⟩
    · exact Or.inl (mem_iUnion.mpr (pair_lifts P F hh s hs))
    · exact Or.inr (mem_iUnion.mpr (pair_lifts P F (hh.exchange F) s hs))

end SuccessorBound

/-- A bound on the old spectrum bounds the entire new spectrum by its successor.
The old seed may have arbitrary disjointifying rank. -/
theorem successorSeed_bounded (P : Seed) {κ : Cardinal.{0}} (inf : ℵ₀ ≤ κ)
    (old : P.Bounded κ) : (successorSeed P).Bounded (Order.succ κ) := by
  intro N E sat
  letI := successorOrder P
  let E₀ : Scott.Model (SuccessorRelation P.R) N := fun r t => E (.old r) t
  let C := smallPresentation (R := P.R) P.mark
  apply SuccessorBound.bound P (E := E₀) inf old C
  obtain ⟨F,hF⟩ := ((successorSeed P).pres.satisfies_iff_backAndForth _ _).mp sat
  let B : BackAndForth (smallModel P.D P.mark) E₀ := {
    matchTuples := F.matchTuples
    atoms := fun h a => by
      cases a with
      | eq i j => exact F.atoms h (.eq i j)
      | rel r s => exact F.atoms h (.rel (.old r) s)
    forth := F.forth
    back := F.back }
  exact (C.satisfies_iff_backAndForth _ _).mpr ⟨B,hF⟩

end KnightModel.Transfinite
