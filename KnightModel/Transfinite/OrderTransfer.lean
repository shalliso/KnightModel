import KnightModel.Transfinite.Seed
import KnightModel.RankTwo.ScottRestrictionLabels
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Naming an invariant order in a Scott model

A comparison of target coordinates is read off any simultaneous source lift.
Alignment of two lifts by one automorphism makes the comparison independent of
the choice. In particular it preserves all the finite back-and-forth moves.
-/

namespace KnightModel.Transfinite

open RankTwo.Scott Cardinal
noncomputable section

inductive WithOrder (R : ℕ → Type) : ℕ → Type where
  | old {n} (r : R n) : WithOrder R n
  | le : WithOrder R 2

instance {R : ℕ → Type} [∀ n, Countable (R n)] (n : ℕ) : Countable (WithOrder R n) := by
  let f : WithOrder R n → Option (R n)
    | .old r => some r
    | .le => none
  apply Function.Injective.countable (f := f)
  rintro (_|_) (_|_) h <;> simp_all [f]

variable {R : ℕ → Type} {M N : Type}

def orderedModel [LinearOrder M] (D : Model R M) : Model (WithOrder R) M
  | _, .old r, s => D r s
  | _, .le, s => s 0 ≤ s 1

def orderedSeed [∀ n, Countable (R n)] [Countable M] [LinearOrder M] (D : Model R M)
    (m : M) (r : R 1) (hr : ∀ t, D r t ↔ t 0 = m) : Seed where
  R := WithOrder R
  M := M
  D := orderedModel D
  countRel := inferInstance
  countM := inferInstance
  ord := inferInstance
  mark := m
  leSym := .le
  le_iff _ := Iff.rfl
  markSym := .old r
  mark_iff := hr

def orderedAutHom [LinearOrder M] (D : Model R M) :
    automorphismGroup (orderedModel D) →* automorphismGroup D where
  toFun g := ⟨g.val, fun {_} r t => g.property (.old r) t⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable [LinearOrder M] {D : Model R M} {E : Model R N}

/-- A raw back-and-forth together with invariance of the proposed source order. -/
structure OrderTransfer (D : Model R M) (E : Model R N) where
  F : BackAndForth D E
  empty : F.matchTuples (n := 0) Fin.elim0 Fin.elim0
  pres : Presentation R M
  invariant : ∀ (g : ↥(automorphismGroup D)) (x y : M), x ≤ y ↔ g • x ≤ g • y

namespace OrderTransfer

variable (T : OrderTransfer D E)

theorem exists_lift {n} (t : Tuple N n) : ∃ s, T.F.Lifts s t := by
  induction n with
  | zero =>
    have ht : t = Fin.elim0 := Subsingleton.elim _ _
    exact ⟨_, ht ▸ T.F.lifts_of_match T.empty⟩
  | succ n ih =>
    obtain ⟨s,hs⟩ := ih (Fin.tail t)
    obtain ⟨x,hx⟩ := T.F.closure.back hs (t 0)
    have ht : push (t 0) (Fin.tail t) = t := funext (Fin.cases rfl (fun _ => rfl))
    exact ⟨push x s,ht ▸ hx⟩

def rel (x y : N) : Prop := ∃ s : Tuple M 2, T.F.Lifts s ![x,y] ∧ s 0 ≤ s 1

theorem coord {n} {s : Tuple M n} {t : Tuple N n}
    (h : T.F.Lifts s t) (i j : Fin n) : s i ≤ s j ↔ T.rel (t i) (t j) := by
  have he : t ∘ ![i,j] = ![t i,t j] := by funext k; fin_cases k <;> rfl
  have hh := h.select T.F ![i,j]
  rw [he] at hh
  refine ⟨fun hl => ⟨_,hh,hl⟩, ?_⟩
  rintro ⟨u,hu,hle⟩
  obtain ⟨g,hg⟩ := T.F.lifts_aligned T.pres hh hu
  exact (T.invariant g _ _).mpr (show g • s i ≤ g • s j from (hg 0) ▸ (hg 1) ▸ hle)

@[implicit_reducible] def order : LinearOrder N := by
  classical
  exact {
    le := T.rel
    le_refl := fun x => by
      obtain ⟨s,h⟩ := T.exists_lift ![x]
      exact (T.coord h 0 0).mp le_rfl
    le_trans := fun x y z hxy hyz => by
      obtain ⟨s,h⟩ := T.exists_lift ![x,y,z]
      exact (T.coord h 0 2).mp (((T.coord h 0 1).mpr hxy).trans ((T.coord h 1 2).mpr hyz))
    le_antisymm := fun x y hxy hyx => by
      obtain ⟨s,h⟩ := T.exists_lift ![x,y]
      exact (T.F.closure.atoms h (.eq 0 1)).mp
        (le_antisymm ((T.coord h 0 1).mpr hxy) ((T.coord h 1 0).mpr hyx))
    le_total := fun x y => by
      obtain ⟨s,h⟩ := T.exists_lift ![x,y]
      exact (le_total (s 0) (s 1)).imp (T.coord h 0 1).mp (T.coord h 1 0).mp
    toDecidableLE := Classical.decRel _
  }

theorem lt_iff {n} {s : Tuple M n} {t : Tuple N n} (h : T.F.Lifts s t) (i j : Fin n) :
    letI := T.order
    s i < s j ↔ t i < t j := by
  letI := T.order
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  exact and_congr (T.coord h i j) (not_congr (T.coord h j i))

def expanded : letI := T.order; BackAndForth (orderedModel D) (orderedModel E) := by
  letI := T.order
  exact {
    matchTuples := T.F.Lifts
    atoms := fun h a => by
      cases a with
      | eq i j => exact T.F.closure.atoms h (.eq i j)
      | rel r p =>
        cases r with
        | old r => exact T.F.closure.atoms h (.rel r p)
        | le => exact T.coord h (p 0) (p 1)
    forth := T.F.closure.forth
    back := T.F.closure.back
  }

theorem satisfies (C : Presentation (WithOrder R) M) :
    letI := T.order
    BackAndForth.Satisfies (orderedModel E) (C.sentence (orderedModel D)) := by
  letI := T.order
  exact (C.satisfies_iff_backAndForth _ _).mpr ⟨T.expanded,T.F.lifts_of_match T.empty⟩

end OrderTransfer
end
end KnightModel.Transfinite
