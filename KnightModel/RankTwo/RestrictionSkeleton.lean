import KnightModel.RankTwo.RestrictionTree

/-! # Building the two comparison chains

The same selection argument chooses the ω₂-skeleton in a large singleton
orbit and the ω₁-subchain in an uncountable relative orbit. It only uses the
size of the principal lower sets and pairwise comparison.
-/

namespace KnightModel.RankTwo.Restriction

open Cardinal Set

private theorem small_union {X I : Type} {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ)
    (smallIndex : #I ≤ κ) (cone : I → Set X) (small : ∀ i, #(cone i) ≤ κ) :
    #(⋃ i, cone i) ≤ κ := calc
  #(⋃ i, cone i) ≤ Cardinal.sum (fun i => #(cone i)) := mk_iUnion_le_sum_mk
  _ ≤ Cardinal.sum (fun _ : I => κ) := Cardinal.sum_le_sum _ _ small
  _ = #I * κ := sum_const' _ _
  _ ≤ κ * κ := mul_le_mul' smallIndex le_rfl
  _ = κ := mul_eq_self hκ

/-- All points in a family of size at most κ have a common upper comparison
witness when the ambient orbit has size greater than κ. -/
theorem common_comparison_witness {X I : Type} {κ : Cardinal.{0}}
    (hκ : ℵ₀ ≤ κ) (large : κ < #X) (hI : #I ≤ κ)
    (lower : X → Set X) (small : ∀ x, #(lower x) ≤ κ)
    (compare : ∀ x y, x ∈ lower y ∨ y ∈ lower x) (u : I → X) :
    ∃ x, ∀ i, u i ∈ lower x ∧ x ∉ lower (u i) := by
  classical
  have hs := small_union hκ hI (fun i => lower (u i)) (fun i => small (u i))
  have h : ∃ x, x ∉ ⋃ i, lower (u i) := by
    by_contra! hn
    have he : (⋃ i, lower (u i)) = Set.univ := eq_univ_of_forall hn
    exact large.not_ge (by simpa only [he, mk_univ] using hs)
  obtain ⟨x, hx⟩ := h
  refine ⟨x, fun i => ?_⟩
  have hi : x ∉ lower (u i) := fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)
  exact ⟨(compare (u i) x).resolve_right hi, hi⟩

section Recursion

variable {I X : Type} [LinearOrder I] [WellFoundedLT I] (lower : X → Set X)
    (chooseNext : ∀ i : I, ∀ u : Iio i → X, ∃ x, ∀ j, u j ∈ lower x ∧ x ∉ lower (u j))

private noncomputable def comparisonSequence : I → X :=
  wellFounded_lt.fix fun i ih => (chooseNext i (fun j => ih j.val j.property)).choose

private theorem comparisonSequence_spec {i j : I} (h : i < j) :
    comparisonSequence lower chooseNext i ∈ lower (comparisonSequence lower chooseNext j) ∧
    comparisonSequence lower chooseNext j ∉ lower (comparisonSequence lower chooseNext i) := by
  let u (k : Iio j) := comparisonSequence lower chooseNext k.val
  have he : comparisonSequence lower chooseNext j = (chooseNext j u).choose := by
    unfold comparisonSequence
    rw [WellFounded.fix_eq]
    rfl
  rw [he]
  exact (chooseNext j u).choose_spec ⟨i, h⟩

end Recursion

/-- A strict chain of the indicated initial ordinal can be selected in any
large pairwise comparable family with κ-small lower cones. -/
theorem comparison_chain {X I : Type} [LinearOrder I] [WellFoundedLT I]
    {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (large : κ < #X) (initial : ∀ i : I, #(Iio i) ≤ κ)
    (lower : X → Set X) (small : ∀ x, #(lower x) ≤ κ)
    (compare : ∀ x y, x ∈ lower y ∨ y ∈ lower x) :
    ∃ e : I ↪ X, ∀ i j, i < j → e i ∈ lower (e j) ∧ e j ∉ lower (e i) := by
  let next := fun i => common_comparison_witness hκ large (initial i) lower small compare
  let f := comparisonSequence lower next
  have hs {i j : I} (h : i < j) : f i ∈ lower (f j) ∧ f j ∉ lower (f i) :=
    comparisonSequence_spec lower next h
  have ne {i j : I} (h : i < j) (eq : f i = f j) : False := by
    have h₁ := (hs h).1
    have h₂ := (hs h).2
    rw [eq] at h₁ h₂
    exact h₂ h₁
  refine ⟨⟨f, fun {i j} eq => ?_⟩, fun i j h => hs h⟩
  rcases lt_trichotomy i j with h | h | h
  · exact (ne h eq).elim
  · exact h
  · exact (ne h eq.symm).elim

/-- The large rank-two singleton orbit admits an ω₂-long comparison skeleton. -/
theorem omegaTwo_skeleton {X : Type} (large : ℵ₁ < #X) (lower : X → Set X)
    (small : ∀ x, #(lower x) ≤ ℵ₁) (compare : ∀ x y, x ∈ lower y ∨ y ∈ lower x) :
    ∃ e : OmegaTwo ↪ X, ∀ i j, i < j → e i ∈ lower (e j) ∧ e j ∉ lower (e i) := by
  apply comparison_chain (aleph0_le_aleph 1) large _ lower small compare
  intro i
  apply Order.lt_succ_iff.mp
  simpa only [succ_aleph, one_add_one_eq_two, mk_toType, card_ord] using mk_Iio_lt i (by simp)

/-- On an uncountable rank-one comparison orbit one can select an ω₁-chain. -/
theorem omegaOne_comparison_subchain {X : Type} (large : ℵ₀ < #X) (lower : X → Set X)
    (small : ∀ x, (lower x).Countable) (compare : ∀ x y, x ∈ lower y ∨ y ∈ lower x) :
    ∃ e : OmegaOne ↪ X, ∀ i j, i < j → e i ∈ lower (e j) ∧ e j ∉ lower (e i) := by
  apply comparison_chain le_rfl large _ lower (fun x => le_aleph0_iff_set_countable.mpr (small x))
    compare
  intro i
  exact lt_aleph_one_iff.mp (by simpa using mk_Iio_lt i (by simp))

end KnightModel.RankTwo.Restriction
