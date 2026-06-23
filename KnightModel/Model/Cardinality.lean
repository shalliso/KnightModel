/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Instance
import Mathlib.Order.Cofinal
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.SetTheory.Ordinal.Family
/-! ## Cardinality of Knight Models

In this file we establish that every `KnightModel` has cardinality at most `ℵ₁`.

The key steps are:
1. Any countable cofinal subset witnesses countability of the model.
2. In an uncountable model, every countable subset has a strict upper bound.
3. This allows a cofinal ω₁-sequence to be built by transfinite recursion.
4. The cofinal sequence gives a surjection from a sigma type of size `ℵ₁ × ℵ₀ = ℵ₁` onto `α`,
   so `#α ≤ ℵ₁`.

## Main results

- `KnightModel.knightModel_card_le_aleph_one`: `#α ≤ Cardinal.aleph 1`

-/

open Cardinal

namespace KnightModel

variable {Ω : Type 0} [Blueprint Ω]
variable {α : Type 0} [KnightModel α Ω]

/-! ### Countability lemmas -/

/-- The downward closure of a countable family in a KnightModel is countable:
    each `{x | x ≤ f i}` is countable by `countable_initialSegment_le`,
    and a countable union of countable sets is countable. -/
lemma countable_iUnion_Iic {ι : Type 0} [Countable ι] (f : ι → α) :
    Countable {x : α // ∃ i, x ≤ f i} := by
  haveI : ∀ i : ι, Countable {x : α // x ≤ f i} := fun i =>
    countable_initialSegment_le (f i)
  have hsurj : Function.Surjective
      (fun p : Σ i : ι, {x : α // x ≤ f i} => (⟨p.2.1, p.1, p.2.2⟩ : {x : α // ∃ i, x ≤ f i})) :=
    fun ⟨x, i, hi⟩ => ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩
  exact hsurj.countable

/-- If a KnightModel has a countable cofinal family, it is itself countable. -/
lemma countable_of_countable_cofinal {ι : Type 0} [Countable ι] (f : ι → α)
    (hcof : ∀ a : α, ∃ i, a ≤ f i) : Countable α := by
  haveI := countable_iUnion_Iic (Ω := Ω) f
  exact Function.Injective.countable
    (f := fun a : α => (⟨a, hcof a⟩ : {x : α // ∃ i, x ≤ f i}))
    (fun a b h => congrArg Subtype.val h)

/-- In an uncountable KnightModel, every countable family has a strict upper bound. -/
lemma exists_strictUpperBound_of_countable [Nonempty α] (hα : ¬ Countable α)
    {ι : Type 0} [Countable ι] (f : ι → α) :
    ∃ a : α, ∀ i, f i < a := by
  by_contra h
  push Not at h
  exact hα (countable_of_countable_cofinal (Ω := Ω) f
    (fun a => let ⟨i, hi⟩ := h a; ⟨i, hi⟩))

/-! ### Cofinal ω₁-sequence -/

/-- Auxiliary: a cofinal sequence on all ordinals by well-founded recursion.
    At each ordinal `o`:
    - if `o < ω₁`, pick a strict upper bound of all previous values
      (well-defined since `o.ToType` is countable for `o < ω₁`)
    - otherwise, return an arbitrary element (dead code for ordinals we care about) -/
private noncomputable def cofinalSeq_aux [Nonempty α] (hα : ¬ Countable α) :
    Ordinal.{0} → α :=
  WellFounded.fix wellFounded_lt fun o ih =>
    if ho : o < (aleph 1).ord then
      haveI : Countable o.ToType := by
        rw [← Set.countable_univ_iff, Cardinal.le_aleph0_iff_set_countable.symm]
        simp only [Cardinal.mk_univ, Cardinal.mk_toType]
        exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp ho)
      (exists_strictUpperBound_of_countable (Ω := Ω) hα
        (fun (j : o.ToType) => ih j.toOrd (Ordinal.typein_lt_self j))).choose
    else Classical.arbitrary α

/-- A cofinal ω₁-sequence in an uncountable KnightModel. -/
noncomputable def cofinalSeq [Nonempty α] (hα : ¬ Countable α) :
    (aleph 1).ord.ToType → α :=
  fun i => cofinalSeq_aux (Ω := Ω) hα i.toOrd

/-- Key bound: for `o' < o < ω₁`, the auxiliary sequence value at `o'` is below that at `o`. -/
private lemma cofinalSeq_aux_lt [Nonempty α] (hα : ¬ Countable α)
    (o' o : Ordinal) (ho : o < (aleph 1).ord) (ho' : o' < o) :
    cofinalSeq_aux (Ω := Ω) hα o' < cofinalSeq_aux (Ω := Ω) hα o := by
  have hCount : Countable o.ToType := by
    rw [← Set.countable_univ_iff, Cardinal.le_aleph0_iff_set_countable.symm]
    simp only [Cardinal.mk_univ, Cardinal.mk_toType]
    exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp ho)
  have heq : cofinalSeq_aux (Ω := Ω) hα o =
      (exists_strictUpperBound_of_countable (Ω := Ω) hα
        (fun j : o.ToType => cofinalSeq_aux (Ω := Ω) hα ↑j.toOrd)).choose := by
    simp only [cofinalSeq_aux]
    rw [WellFounded.fix_eq]
    simp only [dif_pos ho]
  rw [heq]
  let k₀ : o.ToType := Ordinal.ToType.mk ⟨o', ho'⟩
  have hk₀ : (↑k₀.toOrd : Ordinal) = o' :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨o', ho'⟩)
  calc cofinalSeq_aux (Ω := Ω) hα o'
      = cofinalSeq_aux (Ω := Ω) hα ↑k₀.toOrd := by rw [hk₀]
    _ < _ := (exists_strictUpperBound_of_countable (Ω := Ω) hα
                (fun j : o.ToType => cofinalSeq_aux (Ω := Ω) hα ↑j.toOrd)).choose_spec k₀

/-- The cofinal sequence is strictly monotone. -/
lemma cofinalSeq_strictMono [Nonempty α] (hα : ¬ Countable α) :
    StrictMono (cofinalSeq (Ω := Ω) hα) := by
  intro i j hij
  simp only [cofinalSeq]
  apply cofinalSeq_aux_lt (Ω := Ω) hα ↑(i.toOrd) ↑(j.toOrd) (Ordinal.typein_lt_self j)
  exact Ordinal.ToType.mk.symm.strictMono hij

/-- The cofinal sequence is cofinal: every element of α is below some value in the sequence. -/
lemma cofinalSeq_cofinal [Nonempty α] (hα : ¬ Countable α) :
    ∀ a : α, ∃ i, a ≤ cofinalSeq (Ω := Ω) hα i := by
  intro a
  by_contra hne
  push Not at hne
  have hmono := cofinalSeq_strictMono (Ω := Ω) hα
  haveI : Countable (InitialSegment α a) := countable_initialSegment a
  have hCountDom : Countable (aleph 1).ord.ToType := by
    apply Function.Injective.countable
      (f := fun i => (⟨cofinalSeq (Ω := Ω) hα i, hne i⟩ : InitialSegment α a))
    intro i j h
    exact hmono.injective (congrArg Subtype.val h)
  have huncountable : ¬ Countable (aleph 1).ord.ToType := by
    rw [← Cardinal.mk_le_aleph0_iff]
    push Not
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.aleph0_lt_aleph_one
  exact huncountable hCountDom

/-! ### Cardinality bound -/

/-- Every KnightModel has cardinality at most `ℵ₁`.

If `α` is uncountable, build a cofinal ω₁-sequence `cofinalSeq`.
Every element of `α` lies below some `cofinalSeq i`, so the projection
`(i, x : {y // y ≤ cofinalSeq i}) ↦ x` is a surjection from a sigma type of size
`ℵ₁ × ℵ₀ = ℵ₁` onto `α`. -/
theorem knightModel_card_le_aleph_one {Ω : Type 0} [Blueprint Ω]
    {α : Type 0} [KnightModel α Ω] : #α ≤ aleph 1 := by
  rcases isEmpty_or_nonempty α with ⟨⟩ | hα
  · simp
  · haveI : Nonempty α := hα
    by_cases hc : Countable α
    · exact (mk_le_aleph0_iff.mpr hc).trans (aleph0_le_aleph 1)
    · have hsurj : Function.Surjective
          (fun p : Σ i : (aleph 1).ord.ToType, {x : α // x ≤ cofinalSeq hc i} => p.2.1) :=
        fun a =>
          let ⟨i, hi⟩ := cofinalSeq_cofinal hc a
          ⟨⟨i, a, hi⟩, rfl⟩
      calc #α
          ≤ #(Σ i : (aleph 1).ord.ToType, {x : α // x ≤ cofinalSeq hc i}) :=
            mk_le_of_surjective hsurj
        _ = Cardinal.sum (fun i : (aleph 1).ord.ToType => #{x : α // x ≤ cofinalSeq hc i}) :=
            mk_sigma _
        _ ≤ Cardinal.sum (fun _ : (aleph 1).ord.ToType => ℵ₀) :=
            Cardinal.sum_le_sum _ _ fun i => mk_le_aleph0_iff.mpr (countable_initialSegment_le _)
        _ = #((aleph 1).ord.ToType) * ℵ₀ := Cardinal.sum_const' _ _
        _ = ℵ₁ * ℵ₀ := by rw [mk_toType, card_ord]
        _ ≤ ℵ₁ :=
            calc ℵ₁ * ℵ₀ ≤ ℵ₁ * ℵ₁ := mul_le_mul' le_rfl (aleph0_le_aleph 1)
              _ = ℵ₁ := Cardinal.mul_eq_self (aleph0_le_aleph 1)

end KnightModel
