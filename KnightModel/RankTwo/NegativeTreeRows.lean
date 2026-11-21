import KnightModel.RankTwo.RestrictionCardinal
import KnightModel.RankTwo.RestrictionSkeleton
import KnightModel.RankTwo.RestrictionSpecial
import Mathlib.Order.Lattice.Nat

/-! # The actual colored rows obtained from an arbitrary rank-two Scott model

A row color names a source lift of relative rank at most one. A witness-clause
color has an altogether countable fiber. For every other color the comparison
relation is definable dependence at the row endpoint.
-/

namespace KnightModel.RankTwo.Scott.Negative

open Cardinal Set Restriction

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

noncomputable abbrev F : BackAndForth D E := C.system D E sat
abbrev singleton {X : Type} (x : X) := push x (Fin.elim0 : Tuple X 0)

theorem lifts_iff_label {n} (s : Tuple M n) (t : Tuple N n) :
    (F C sat).Lifts s t ↔ (C.label D s).Holds E t := by
  refine ⟨fun h => ((F C sat).closure.holds_iff _ h).mp (C.self_label D s), ?_⟩
  exact (F C sat).lifts_of_match (s := s) (t := t)

/-- Extract a large actual singleton fiber and a strictly increasing comparison skeleton in it. -/
theorem big_skeleton (size : aleph 2 ≤ #N) (rank : ∀ x, ModelRankLE D 2 [] x) :
    ∃ (x : M) (e : OmegaTwo ↪ orbitFiber (F C sat) Fin.elim0 x Fin.elim0),
      ℵ₁ < #(orbitFiber (F C sat) Fin.elim0 x Fin.elim0) ∧
      ∀ a b, a < b → (e a).val ∈ lowFiber (F C sat) 1 (singleton (e b).val) := by
  haveI : Countable M := Function.Surjective.countable C.onto
  have allPoint (y : N) : ∃ x : M, y ∈ orbitFiber (F C sat) Fin.elim0 x Fin.elim0 := by
    obtain ⟨x,h⟩ := (F C sat).back (s := Fin.elim0) (t := Fin.elim0) ((C.sentence_iff D E).mp sat).1 y
    exact ⟨x,(F C sat).lifts_of_match h⟩
  let f (y : N) := (allPoint y).choose
  have oneTwo : ℵ₁ < aleph.{0} 2 := aleph_lt_aleph.mpr _root_.one_lt_two
  have hr : Cardinal.IsRegular (aleph.{0} 2) := by
    simpa only [one_add_one_eq_two] using isRegular_aleph_add_one 1
  obtain ⟨x,hx⟩ := infinite_pigeonhole_card f (aleph 2) size (aleph0_le_aleph 2)
    (by rw [hr.cof_ord]; exact (mk_le_aleph0 (α := M)).trans_lt (aleph0_lt_aleph_one.trans oneTwo))
  let O := orbitFiber (F C sat) Fin.elim0 x Fin.elim0
  have sub : f ⁻¹' {x} ⊆ O := by
    intro y hy
    change y ∈ orbitFiber _ _ x _
    rw [← (show f y = x from hy)]
    exact (allPoint y).choose_spec
  have big : ℵ₁ < #O := oneTwo.trans_le (hx.trans (mk_le_mk_of_subset sub))
  have memO : O.Nonempty := by
    by_contra h
    simpa [not_nonempty_iff_eq_empty.mp h] using big
  have r : ModelRankLE D (1+1) (List.ofFn (Fin.elim0 : Tuple M 0)) x := by simpa using rank x
  have cmp := orbitFiber_dichotomy (F C sat) C Fin.elim0 x Fin.elim0 r memO
  rcases cmp with ⟨d,cap⟩ | pair
  · exact False.elim (big.not_ge ((mk_le_mk_of_subset cap).trans (by simpa using lowFiber_cardinal (F C sat) C 1 (singleton d))))
  · let cone (z : O) : Set O := Subtype.val ⁻¹' lowFiber (F C sat) 1 (singleton z.val)
    have bound (z : O) : #(cone z) ≤ ℵ₁ := by
      let g (w : cone z) : lowFiber (F C sat) 1 (singleton z.val) := ⟨w.val.val,w.property⟩
      have inj : Function.Injective g := fun a b h =>
        Subtype.ext (Subtype.ext (congrArg (fun v : lowFiber (F C sat) 1 (singleton z.val) => v.val) h))
      exact (mk_le_of_injective inj).trans (by simpa using lowFiber_cardinal (F C sat) C 1 (singleton z.val))
    obtain ⟨e,he⟩ := omegaTwo_skeleton big cone bound
      (fun y z => (pair y.val y.property z.val z.property).symm)
    exact ⟨x,e,big,fun a b h => (he a b h).1⟩

/-- Enumerate the source pair labels of relative rank at most one. -/
def sourceHead (k : Nat) : M := C.tuples 2 k 0
def sourceBase (k : Nat) : Tuple M 1 := fun l => C.tuples 2 k l.succ

def colorTests (a b : N) : Set Nat := {k |
  ModelRankLE D 1 (List.ofFn (sourceBase C k)) (sourceHead C k) ∧
    a ∈ orbitFiber (F C sat) (sourceBase C k) (sourceHead C k) (singleton b)}

noncomputable def color (a b : N) : Nat := sInf (colorTests C sat a b)

theorem color_spec {a b : N} (ab : a ∈ lowFiber (F C sat) 1 (singleton b)) :
    color C sat a b ∈ colorTests C sat a b := by
  obtain ⟨u,s,rank,lab⟩ := ab
  obtain ⟨k,hk⟩ := C.tuples_onto (push u s)
  refine Nat.sInf_mem ⟨k,?_⟩
  have h₁ : sourceHead C k = u := congrFun hk 0
  have h₂ : sourceBase C k = s := funext fun i => congrFun hk i.succ
  change _ ∧ a ∈ orbitFiber _ _ _ _
  rw [h₁,h₂]
  exact ⟨rank,lab⟩

def witnessColor (k : Nat) : Prop :=
  ∃ w : M, ∀ w', Conjugate ↥(automorphismGroup D) (List.ofFn (sourceBase C k)) w w' →
    ModelRankLE D 0 (w' :: List.ofFn (sourceBase C k)) (sourceHead C k)

/-- The relation is universal on a countable witness-clause fiber. All other
colors use rank-zero dependence over the endpoint and the second argument. -/
noncomputable def rows (e : OmegaTwo ↪ N) (b : OmegaTwo) : Chart OmegaTwo where
  color x := color C sat (e x) (e b)
  rel x y := witnessColor (D := D) C (color C sat (e x) (e b)) ∨
    e x ∈ lowFiber (F C sat) 0 (push (e y) (singleton (e b)))

theorem rows_local (e : OmegaTwo ↪ N)
    (chain : ∀ a b, a < b → e a ∈ lowFiber (F C sat) 1 (singleton (e b))) :
    LocalCharts (rows C sat e) where
  compare := by
    intro b x y xb yb same
    let k := color C sat (e x) (e b)
    have ky : color C sat (e y) (e b) = k := same.symm
    obtain ⟨rank,hx⟩ := color_spec C sat (chain x b xb)
    have hy := (color_spec C sat (chain y b yb)).2
    rw [ky] at hy
    by_cases w : witnessColor (D := D) C k
    · exact Or.inl (Or.inl w)
    · obtain h | h := orbitFiber_compare (F C sat) C _ _ _ (rank.resolve_left w) _ hx _ hy
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)
  small := by
    intro b x xb
    let k := color C sat (e x) (e b)
    obtain ⟨rank,hx⟩ := color_spec C sat (chain x b xb)
    have count0 (t : Tuple N 2) : (lowFiber (F C sat) 0 t).Countable :=
      le_aleph0_iff_set_countable.mp (by simpa using lowFiber_cardinal (F C sat) C 0 t)
    by_cases w : witnessColor (D := D) C k
    · obtain ⟨d, cap⟩ := orbitFiber_witness (F C sat) C _ _ (singleton (e b)) w ⟨e x,hx⟩
      apply ((count0 (push d (singleton (e b)))).preimage e.injective).mono
      rintro y ⟨yb,c,_⟩
      have hy := (color_spec C sat (chain y b yb)).2
      change color C sat (e y) (e b) = k at c
      rw [c] at hy
      exact cap hy
    · apply ((count0 (push (e x) (singleton (e b)))).preimage e.injective).mono
      rintro y ⟨yb,c,r⟩
      change color C sat (e y) (e b) = k at c
      exact r.resolve_left (fun wy => w (c ▸ wy))

end KnightModel.RankTwo.Scott.Negative
