/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Chain.Colimit
import Mathlib.Order.Zorn
/-!
# Knight Chains: Zorn Application and Uncountability Theorem

This file applies Zorn's lemma to produce a `KnightChain` of full-domain, i.e. of length
omega_1, and uses it to produce an uncountable Knight model.

## Main results

* `KnightChain.exists_fullDomain`: there exists a `KnightChain` with `dom = Set.univ`
* `KnightChain.exists_uncountable_knightModel`: for any `Blueprint Ω`, there exists
  an uncountable `KnightModel Ω`

## Tags

knight chain, Zorn, uncountable, omega1
-/

namespace KnightChain

variable {Ω : Type 0} [Blueprint Ω]
variable {K : Type 0} [KnightModel K Ω] [Countable K] [Nonempty K]
variable (c : KnightChain Ω K)
variable [Nonempty c.dom]

/-! ### Extension preorder on `KnightChain` -/

/-- The extension preorder: `c1 ≤ c2` iff `c2` has at least the same domain as `c1` and agrees
with `c1` on all shared indices. -/
instance instPreorderKnightChain : Preorder (KnightChain Ω K) where
  le c1 c2 := ∃ h : c1.dom ⊆ c2.dom,
    ∀ (i j : c1.dom), c2.emb ⟨i.val, h i.property⟩ ⟨j.val, h j.property⟩ = c1.emb i j
  le_refl c := ⟨Set.Subset.refl _, fun i j => by congr 1⟩
  le_trans c1 c2 c3 h12 h23 := by
    obtain ⟨h12sub, h12emb⟩ := h12
    obtain ⟨h23sub, h23emb⟩ := h23
    refine ⟨h12sub.trans h23sub, fun i j => ?_⟩
    have e := h23emb ⟨i.val, h12sub i.property⟩ ⟨j.val, h12sub j.property⟩
    rw [show (⟨i.val, h23sub (h12sub i.property)⟩ : c3.dom) =
            ⟨i.val, (h12sub.trans h23sub) i.property⟩ from Subtype.ext rfl,
        show (⟨j.val, h23sub (h12sub j.property)⟩ : c3.dom) =
            ⟨j.val, (h12sub.trans h23sub) j.property⟩ from Subtype.ext rfl] at e
    exact e.trans (h12emb i j)

omit [Nonempty c.dom] in
/-- The empty chain: trivially a valid `KnightChain`. -/
noncomputable def emptyChain : KnightChain Ω K where
  dom := ∅
  dom_initial _ hx := absurd hx (Set.mem_empty_iff_false _ |>.mp hx).elim
  emb i := absurd i.property (Set.mem_empty_iff_false _ |>.mp i.property).elim
  emb_rfl i := absurd i.property (Set.mem_empty_iff_false _ |>.mp i.property).elim
  emb_trans {i} _ _ := absurd i.property (Set.mem_empty_iff_false _ |>.mp i.property).elim
  emb_range_in_nontrivial {i} _ _ :=
    absurd i.property (Set.mem_empty_iff_false _ |>.mp i.property).elim

omit [Nonempty c.dom] in
instance instNonemptyKnightChain : Nonempty (KnightChain Ω K) :=
  ⟨emptyChain⟩

omit [Nonempty c.dom] in
lemma emptyChain_le (d : KnightChain Ω K) : emptyChain (Ω := Ω) (K := K) ≤ d :=
  ⟨Set.empty_subset _, fun i => absurd i.property (Set.mem_empty_iff_false _ |>.mp i.property).elim⟩

/-! ### Chain upper bound construction -/

/-- In a chain `S` of `KnightChain`s, any two elements of the union `⋃ c ∈ S, c.dom`
are both contained in some single member of `S`. -/
private lemma exists_chain_containing_pair
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S)
    (i j : (⋃ c ∈ S, c.dom).Elem) :
    ∃ c ∈ S, i.val ∈ c.dom ∧ j.val ∈ c.dom := by
  obtain ⟨ci, hciS, hici⟩ := Set.mem_iUnion₂.mp i.property
  obtain ⟨cj, hcjS, hjcj⟩ := Set.mem_iUnion₂.mp j.property
  rcases eq_or_ne ci cj with rfl | hne
  · exact ⟨ci, hciS, hici, hjcj⟩
  · rcases hS hciS hcjS hne with ⟨hsub, _⟩ | ⟨hsub, _⟩
    · exact ⟨cj, hcjS, hsub hici, hjcj⟩
    · exact ⟨ci, hciS, hici, hsub hjcj⟩

/-- In a chain `S` of `KnightChain`s, any three elements of the union `⋃ c ∈ S, c.dom`
are all contained in some single member of `S`. -/
private lemma exists_chain_containing_triple
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S)
    (i j k : (⋃ c ∈ S, c.dom).Elem) :
    ∃ c ∈ S, i.val ∈ c.dom ∧ j.val ∈ c.dom ∧ k.val ∈ c.dom := by
  obtain ⟨c1, hc1S, hi1, hj1⟩ := exists_chain_containing_pair S hS i j
  obtain ⟨c2, hc2S, hj2, hk2⟩ := exists_chain_containing_pair S hS j k
  rcases eq_or_ne c1 c2 with rfl | hne
  · exact ⟨c1, hc1S, hi1, hj1, hk2⟩
  · rcases hS hc1S hc2S hne with ⟨hsub, _⟩ | ⟨hsub, _⟩
    · exact ⟨c2, hc2S, hsub hi1, hsub hj1, hk2⟩
    · exact ⟨c1, hc1S, hi1, hj1, hsub hk2⟩

/-- Any two chains in `S` that both contain `x` and `y` give the same embedding value. -/
private lemma emb_agree_of_mem_chain
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S)
    (c1 c2 : KnightChain Ω K) (hc1S : c1 ∈ S) (hc2S : c2 ∈ S)
    {x y : Omega1} (hi1 : x ∈ c1.dom) (hj1 : y ∈ c1.dom)
    (hi2 : x ∈ c2.dom) (hj2 : y ∈ c2.dom) :
    c1.emb ⟨x, hi1⟩ ⟨y, hj1⟩ = c2.emb ⟨x, hi2⟩ ⟨y, hj2⟩ := by
  rcases eq_or_ne c1 c2 with rfl | hne
  · congr 1
  · rcases hS hc1S hc2S hne with ⟨hsub, hemb⟩ | ⟨hsub, hemb⟩
    · have h := hemb ⟨x, hi1⟩ ⟨y, hj1⟩
      rw [show (⟨x, hsub hi1⟩ : c2.dom) = ⟨x, hi2⟩ from Subtype.ext rfl,
          show (⟨y, hsub hj1⟩ : c2.dom) = ⟨y, hj2⟩ from Subtype.ext rfl] at h
      exact h.symm
    · have h := hemb ⟨x, hi2⟩ ⟨y, hj2⟩
      rw [show (⟨x, hsub hi2⟩ : c1.dom) = ⟨x, hi1⟩ from Subtype.ext rfl,
          show (⟨y, hsub hj2⟩ : c1.dom) = ⟨y, hj1⟩ from Subtype.ext rfl] at h
      exact h

/-- The upper bound of a chain `S` of `KnightChain`s. -/
noncomputable def chainUB
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S) :
    KnightChain Ω K where
  dom := ⋃ c ∈ S, c.dom
  dom_initial x hx y hyx :=
    let ⟨c, hcS, hxc⟩ := Set.mem_iUnion₂.mp hx
    Set.mem_iUnion₂.mpr ⟨c, hcS, c.dom_initial x hxc y hyx⟩
  emb i j :=
    let h := exists_chain_containing_pair S hS i j
    h.choose.emb ⟨i.val, h.choose_spec.2.1⟩ ⟨j.val, h.choose_spec.2.2⟩
  emb_rfl i := by
    have h := exists_chain_containing_pair S hS i i
    change h.choose.emb ⟨i.val, h.choose_spec.2.1⟩ ⟨i.val, h.choose_spec.2.2⟩ = _
    rw [show (⟨i.val, h.choose_spec.2.2⟩ : h.choose.dom) = ⟨i.val, h.choose_spec.2.1⟩
            from Subtype.ext rfl]
    exact h.choose.emb_rfl _
  emb_trans {i} {j} {k} hij hjk := by
    obtain ⟨c, hcS, hic, hjc, hkc⟩ := exists_chain_containing_triple S hS i j k
    have h_ik := exists_chain_containing_pair S hS i k
    have h_jk := exists_chain_containing_pair S hS j k
    have h_ij := exists_chain_containing_pair S hS i j
    rw [emb_agree_of_mem_chain S hS _ c h_ik.choose_spec.1 hcS
            h_ik.choose_spec.2.1 h_ik.choose_spec.2.2 hic hkc,
        emb_agree_of_mem_chain S hS _ c h_jk.choose_spec.1 hcS
            h_jk.choose_spec.2.1 h_jk.choose_spec.2.2 hjc hkc,
        emb_agree_of_mem_chain S hS _ c h_ij.choose_spec.1 hcS
            h_ij.choose_spec.2.1 h_ij.choose_spec.2.2 hic hjc]
    rw [← c.emb_trans (show (⟨i.val, hic⟩ : c.dom) ≤ ⟨j.val, hjc⟩ from hij)
                      (show (⟨j.val, hjc⟩ : c.dom) ≤ ⟨k.val, hkc⟩ from hjk)]
  emb_range_in_nontrivial {i} {j} hlt x := by
    obtain ⟨c, hcS, hic, hjc⟩ := exists_chain_containing_pair S hS i j
    have h := exists_chain_containing_pair S hS i j
    change ∃ y : K, (h.choose.emb ⟨i.val, h.choose_spec.2.1⟩ ⟨j.val, h.choose_spec.2.2⟩) x
        = embKNontrivial y
    rw [emb_agree_of_mem_chain S hS _ c h.choose_spec.1 hcS
            h.choose_spec.2.1 h.choose_spec.2.2 hic hjc]
    exact c.emb_range_in_nontrivial (show (⟨i.val, hic⟩ : c.dom) < ⟨j.val, hjc⟩ from hlt) x

/-- Rewrite `chainUB.emb` in terms of any particular chain containing the two indices. -/
private lemma chainUB_emb_eq
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S)
    (i j : (chainUB S hS).dom)
    (c : KnightChain Ω K) (hcS : c ∈ S) (hic : i.val ∈ c.dom) (hjc : j.val ∈ c.dom) :
    (chainUB S hS).emb i j = c.emb ⟨i.val, hic⟩ ⟨j.val, hjc⟩ :=
  emb_agree_of_mem_chain S hS
      (exists_chain_containing_pair S hS i j).choose c
      (exists_chain_containing_pair S hS i j).choose_spec.1 hcS
      (exists_chain_containing_pair S hS i j).choose_spec.2.1
      (exists_chain_containing_pair S hS i j).choose_spec.2.2
      hic hjc

/-- Every chain in `S` is ≤ `chainUB S`. -/
lemma le_chainUB
    (S : Set (KnightChain Ω K)) (hS : IsChain (· ≤ ·) S)
    (d : KnightChain Ω K) (hdS : d ∈ S) : d ≤ chainUB S hS := by
  refine ⟨fun _ hx => Set.mem_iUnion₂.mpr ⟨d, hdS, hx⟩, fun i j => ?_⟩
  let i' : (chainUB S hS).dom := ⟨i.val, Set.mem_iUnion₂.mpr ⟨d, hdS, i.property⟩⟩
  let j' : (chainUB S hS).dom := ⟨j.val, Set.mem_iUnion₂.mpr ⟨d, hdS, j.property⟩⟩
  change (chainUB S hS).emb i' j' = d.emb i j
  rw [chainUB_emb_eq S hS i' j' d hdS i.property j.property]

/-! ### Zorn application -/

/-- A `KnightChain` with `dom = Set.Iio α` has countable domain,
since `α` is a countable ordinal. -/
private lemma countable_Iio (α : Omega1) : Countable (Set.Iio α : Set Omega1) := by
  -- α.toOrd.val is a countable ordinal (since it's below (aleph 1).ord), so its ToType
  -- is countable. We inject Set.Iio α into (α.toOrd.val).ToType.
  have hα : (α.toOrd : Ordinal) < (Cardinal.aleph 1).ord := α.toOrd.property
  haveI hCount : Countable (α.toOrd : Ordinal).ToType := by
    rw [← Set.countable_univ_iff, Cardinal.le_aleph0_iff_set_countable.symm]
    simp only [Cardinal.mk_univ, Cardinal.mk_toType]
    exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp hα)
  -- For any x : Omega1 with x < α, we have x.toOrd.val < α.toOrd.val (in Ordinal).
  have h_lt : ∀ x : Omega1, x < α →
      ((x.toOrd : Ordinal) < (α.toOrd : Ordinal)) := fun x hx => by
    have : Ordinal.ToType.mk.symm.toOrderEmbedding x < Ordinal.ToType.mk.symm.toOrderEmbedding α :=
      Ordinal.ToType.mk.symm.lt_iff_lt.mpr hx
    exact this
  apply Function.Injective.countable
    (f := fun x : (Set.Iio α : Set Omega1) =>
      Ordinal.ToType.mk (o := (α.toOrd : Ordinal))
        ⟨(x.val.toOrd : Ordinal), h_lt x.val x.property⟩)
  intro x y hxy
  apply Subtype.ext
  -- ToType.mk is injective; extract equality of underlying Subtype values
  have h1 : (⟨(x.val.toOrd : Ordinal), h_lt x.val x.property⟩ : Set.Iio (α.toOrd : Ordinal))
          = ⟨(y.val.toOrd : Ordinal), h_lt y.val y.property⟩ :=
    Ordinal.ToType.mk.injective hxy
  have h2 : (x.val.toOrd : Ordinal) = (y.val.toOrd : Ordinal) := by
    have := h1
    simpa using congrArg (·.val) this
  -- Convert back through ToType.mk.symm
  have h3 : x.val.toOrd = y.val.toOrd := Subtype.ext h2
  exact Ordinal.ToType.mk.symm.injective h3

/-- The domain of a `KnightChain` is a lower set (initial segment). -/
private lemma dom_isLowerSet (c : KnightChain Ω K) : IsLowerSet c.dom := fun {x y} hyx hx => by
  -- hyx : y ≤ x, hx : x ∈ c.dom
  -- dom_initial says: if x ∈ dom and y < x, then y ∈ dom
  -- We want to use this, but hyx is y ≤ x, not y < x
  by_cases h : y < x
  · exact c.dom_initial x hx y h
  · -- y ≤ x and ¬(y < x), so y = x
    have : x ≤ y := by
      push Not at h
      exact h
    have hyx_eq : y = x := le_antisymm hyx this
    rw [hyx_eq]
    exact hx

/-- A chain `c` with `c.dom = Set.Iio α` is below its one-step extension `c.extend α`. -/
private lemma le_extend_of_dom_eq_Iio (c : KnightChain Ω K) (α : Omega1)
    (hα : c.dom = Set.Iio α) [Countable c.dom] :
    c ≤ c.extend α hα := by
  have hsub_dom : c.dom ⊆ (c.extend α hα).dom := by rw [hα]; exact Set.Iio_subset_Iic_self
  refine ⟨hsub_dom, fun i j => ?_⟩
  have hi : i.val < α := hα.le i.property
  have hj : j.val < α := hα.le j.property
  change (c.extend α hα).emb ⟨i.val, hsub_dom i.property⟩ ⟨j.val, hsub_dom j.property⟩ =
      c.emb i j
  simp only [extend, dif_pos hi, dif_pos hj]

/-- There exists a `KnightChain` with `dom = Set.univ`.
    Proved by applying Zorn's lemma to `KnightChain Ω K`. -/
theorem exists_fullDomain :
    ∃ c : KnightChain Ω K, c.dom = Set.univ := by
  have hUB : ∀ S : Set (KnightChain Ω K), IsChain (· ≤ ·) S → BddAbove S := fun S hS =>
    ⟨chainUB S hS, fun d hdS => le_chainUB S hS d hdS⟩
  obtain ⟨c_max, hmax⟩ := zorn_le hUB
  refine ⟨c_max, ?_⟩
  by_contra hne
  rcases (dom_isLowerSet c_max).eq_univ_or_Iio with heq_univ | ⟨α, hα⟩
  · exact hne heq_univ
  haveI : Countable c_max.dom := by rw [hα]; exact countable_Iio α
  obtain ⟨hsub, _⟩ := hmax (le_extend_of_dom_eq_Iio c_max α hα)
  have hα_cmax : α ∈ c_max.dom := hsub (Set.mem_Iic.mpr le_rfl)
  rw [hα] at hα_cmax
  exact (lt_irrefl α) hα_cmax

/-- For any `Blueprint Ω`, there exists an uncountable `KnightModel Ω`. -/
theorem exists_uncountable_knightModel {Ω : Type 0} [Blueprint Ω] :
    ∃ (α : Type 0), Nonempty (KnightModel α Ω) ∧ ¬ Countable α := by
  -- Use the canonical countable model K
  let K := Blueprint.Model Ω
  haveI : KnightModel K Ω := Blueprint.Model.instKnightModel
  haveI : Countable K := inferInstanceAs (Countable {n : Ω // n < 1})
  haveI : Nonempty K := by
    obtain ⟨x, hx⟩ : ∃ x : Ω, x < 1 := by
      obtain ⟨y, hy⟩ := @NoMinOrder.exists_lt Ω _ _ (1 : Ω)
      exact ⟨y, hy⟩
    exact ⟨⟨x, hx⟩⟩
  -- Get a full-domain chain
  obtain ⟨c, hcdom⟩ := exists_fullDomain (Ω := Ω) (K := K)
  -- c.dom = Set.univ is uncountable (Omega1 is uncountable)
  have huncountable_dom : ¬ Countable c.dom := by
    rw [hcdom]
    intro hcount
    -- c.dom = Set.univ is countable, so Omega1 is countable
    haveI : Countable Omega1 := by
      -- If Set.univ : Set Omega1 is countable, then Omega1 is countable
      exact Set.countable_univ_iff.mp hcount
    have : Cardinal.mk Omega1 ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr inferInstance
    have : Cardinal.aleph 1 ≤ Cardinal.aleph0 := by
      calc Cardinal.aleph 1 = Cardinal.mk Omega1 := by
            rw [Cardinal.mk_toType, Cardinal.card_ord]
          _ ≤ Cardinal.aleph0 := this
    exact absurd this (by exact (not_le.mpr Cardinal.aleph0_lt_aleph_one))
  -- Use the colimit as the uncountable model
  haveI hNonemptyDom : Nonempty c.dom := by
    rw [hcdom]; exact ⟨Classical.arbitrary Omega1, Set.mem_univ _⟩
  haveI : KnightModel c.Colimit Ω := instKnightModelColimit c
  exact ⟨c.Colimit, ⟨instKnightModelColimit c⟩,
    not_countable_colimit c huncountable_dom⟩

end KnightChain
