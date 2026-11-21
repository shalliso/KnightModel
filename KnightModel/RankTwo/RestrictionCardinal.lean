import KnightModel.RankTwo.RestrictionLifts
import KnightModel.RankTwo.RestrictionRankAction
import KnightModel.RankTwo.Cardinality
import Mathlib.SetTheory.Cardinal.Aleph

/-! # The cardinal bound for finite disjointifying rank in arbitrary Scott models

Over a finite tuple in the target, the realizations of all source labels of
rank at most n form a set of size at most ℵₙ. The definition uses the actual
rank of the countable source and lifts through its Scott back-and-forth.
-/

namespace KnightModel.RankTwo.Scott

open Cardinal Set
variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (F : BackAndForth D E) (C : Presentation R M)

/-- The target realizations of a pointed finite source orbit label. -/
def orbitFiber {k : ℕ} (s : Tuple M k) (x : M) (t : Tuple N k) : Set N :=
  {y | F.Lifts (push x s) (push y t)}

/-- The set of target points with a source lift of the indicated relative rank. -/
def lowFiber (n : ℕ) {k : ℕ} (t : Tuple N k) : Set N :=
  {y | ∃ (x : M) (s : Tuple M k), ModelRankLE D n (List.ofFn s) x ∧ y ∈ orbitFiber F s x t}

include C in
private theorem union_of_orbits {n k : ℕ} (t : Tuple N k)
    (bound : ∀ (s : Tuple M k) (x : M), ModelRankLE D n (List.ofFn s) x →
      #(orbitFiber F s x t) ≤ aleph n) : #(lowFiber F n t) ≤ aleph n := by
  classical
  let J := {p : M × Tuple M k // ModelRankLE D n (List.ofFn p.2) p.1}
  haveI : Countable M := Function.Surjective.countable (f := C.enum) C.onto
  let sets (p : J) := orbitFiber F p.val.2 p.val.1 t
  have he : lowFiber F n t = ⋃ p, sets p := by
    ext y
    constructor
    · rintro ⟨x, s, h, hy⟩
      exact mem_iUnion.mpr ⟨⟨(x,s), h⟩, hy⟩
    · intro h
      obtain ⟨p, hp⟩ := mem_iUnion.mp h
      exact ⟨p.val.1, p.val.2, p.property, hp⟩
  rw [he]
  calc
    #(⋃ p, sets p) ≤ Cardinal.sum (fun p => #(sets p)) := mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : J => aleph n) :=
      Cardinal.sum_le_sum _ _ fun p => bound _ _ p.property
    _ = #J * aleph n := sum_const' _ _
    _ ≤ aleph n * aleph n := mul_le_mul' ((mk_le_aleph0 (α := J)).trans (aleph0_le_aleph n)) le_rfl
    _ = aleph n := mul_eq_self (aleph0_le_aleph n)

include C in
private theorem zeroFiber_subsingleton {k : ℕ} (s : Tuple M k) (x : M) (t : Tuple N k)
    (rank : ModelRankLE D 0 (List.ofFn s) x) : (orbitFiber F s x t).Subsingleton := by
  intro y hy z hz
  obtain ⟨x', h⟩ := F.closure.back hy z
  obtain ⟨g, hg, hgx⟩ := F.conjugate_of_lifts C hz (h.eraseSecond F)
  have hx : x = x' := (rank g hg).symm.trans hgx
  exact ((h.head_eq F).mp hx.symm).symm

private theorem transport_witness {G X : Type*} [Group G] [MulAction G X]
    {n : ℕ} {s : List X} {x z c : X} (g : G) (hg : Fixes g s) (hz : g • x = z)
    (hw : ∀ c', Conjugate G s c c' → RankLE G n (c' :: s) x) : RankLE G n (c :: s) z := by
  have hi : Fixes g⁻¹ s := by
    intro v hv
    simpa only [inv_smul_smul] using (congrArg (fun w => g⁻¹ • w) (hg v hv)).symm
  have he : s.map (g • ·) = s := by
    conv_rhs => rw [← List.map_id s]
    exact List.map_congr_left hg
  have h := (hw _ ⟨g⁻¹, hi, rfl⟩).smul g
  simpa only [List.map_cons, smul_inv_smul, he, hz] using h

include C in
/-- Either one target witness captures the entire pointed orbit at the next
lower rank, or every pair is compared at that lower rank. This is the
successor rank dichotomy transferred from the source automorphism group. -/
theorem orbitFiber_dichotomy {n k : ℕ} (s : Tuple M k) (x : M) (t : Tuple N k)
    (rank : ModelRankLE D (n + 1) (List.ofFn s) x) (inhabited : (orbitFiber F s x t).Nonempty) :
    (∃ d, orbitFiber F s x t ⊆ lowFiber F n (push d t)) ∨
    ∀ y ∈ orbitFiber F s x t, ∀ z ∈ orbitFiber F s x t,
      z ∈ lowFiber F n (push y t) ∨ y ∈ lowFiber F n (push z t) := by
  rcases rank with ⟨c, hc⟩ | hc
  · obtain ⟨y₀, hy₀⟩ := inhabited
    obtain ⟨d, hd⟩ := F.closure.forth (hy₀.tail F) c
    refine Or.inl ⟨d, ?_⟩
    intro y hy
    obtain ⟨z, h⟩ := F.closure.back hd y
    obtain ⟨g, hg, hgx⟩ := F.conjugate_of_lifts C hy (h.eraseSecond F)
    refine ⟨z, push c s, ?_, h⟩
    rw [ofFn_push]
    exact transport_witness g hg hgx hc
  · apply Or.inr
    intro y hy z hz
    obtain ⟨x', h⟩ := F.closure.back hz y
    have conj := F.conjugate_of_lifts C hy (h.eraseSecond F)
    rcases hc x' conj with hx | hx'
    · exact Or.inl ⟨x, push x' s, ofFn_push x' s ▸ hx, h.exchange F⟩
    · exact Or.inr ⟨x', push x s, ofFn_push x s ▸ hx', h⟩

include C in
private theorem successorFiber {n k : ℕ} (s : Tuple M k) (x : M) (t : Tuple N k)
    (rank : ModelRankLE D (n + 1) (List.ofFn s) x)
    (ih : ∀ {l}, ∀ u : Tuple N l, #(lowFiber F n u) ≤ aleph n) :
    #(orbitFiber F s x t) ≤ Order.succ (aleph n) := by
  let O := orbitFiber F s x t
  by_cases inhabited : O.Nonempty
  · rcases orbitFiber_dichotomy F C s x t rank inhabited with ⟨d, sub⟩ | cmp
    · exact (mk_le_mk_of_subset sub).trans ((ih _).trans (Order.le_succ _))
    · let lower (y : O) : Set O := Subtype.val ⁻¹' lowFiber F n (push y.val t)
      have small (y : O) : #(lower y) ≤ aleph n := by
        let f (z : lower y) : lowFiber F n (push y.val t) := ⟨z.val.val, z.property⟩
        have inj : Function.Injective f := fun _ _ he =>
          Subtype.ext (Subtype.ext (congrArg (fun w : lowFiber F n (push y.val t) => w.val) he))
        exact (mk_le_of_injective inj).trans (ih _)
      exact cardinal_le_succ_of_pair_cover (aleph0_le_aleph n) lower small
        (fun y z => (cmp _ y.property _ z.property).symm)
  · change #O ≤ _
    simp [Set.not_nonempty_iff_eq_empty.mp inhabited]

include C in
/-- Countably many labels of relative rank at most n over a fixed finite
target tuple together have at most ℵₙ realizations. -/
theorem lowFiber_cardinal (n : ℕ) {k : ℕ} (t : Tuple N k) : #(lowFiber F n t) ≤ aleph n := by
  induction n generalizing k with
  | zero =>
    apply union_of_orbits F C t
    intro s x hx
    simpa only [Nat.cast_zero, aleph_zero] using
      (le_aleph0_iff_set_countable.mpr (zeroFiber_subsingleton F C s x t hx).countable)
  | succ n ih =>
    apply union_of_orbits F C t
    intro s x hx
    simpa only [succ_aleph, Nat.cast_succ] using successorFiber F C s x t hx (fun u => ih u)

/-- Every model of the Scott sentence of a finite-rank structure obeys the
corresponding aleph bound. Specializing to n=2 gives ℵ₂. -/
theorem cardinal_le_aleph_of_scott_rank (n : ℕ) (rank : ∀ x, ModelRankLE D n [] x)
    (sat : BackAndForth.Satisfies E (C.sentence D)) : #N ≤ aleph n := by
  obtain ⟨B, hb⟩ := (C.satisfies_iff_backAndForth D E).mp sat
  have all : lowFiber B n (k := 0) Fin.elim0 = Set.univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := B.back hb y
    exact ⟨x, Fin.elim0, by simpa using rank x, B.lifts_of_match hx⟩
  simpa only [all, mk_univ] using lowFiber_cardinal B C n (k := 0) Fin.elim0

end KnightModel.RankTwo.Scott
