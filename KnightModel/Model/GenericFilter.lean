/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.DenseSets
import KnightModel.Model.Instance
/-!
# Generic Filter for the Model Isomorphism

This file produces a suitably generic filter of `ModelIsoCondition α β Ω` conditions, namely
one that meets all the `inDomain` and `inRange` dense open sets defined in DenseSets.lean.
This results in a `PartialKnightIso` whose domain is all of `α` and range all of `β`.

## Main definitions

* `ModelIsoCondition.denseSets`: all relevant dense sets indexed by `α ⊕ β`
* `ModelIsoCondition.genericFilter`: the resulting generic filter
* `ModelIsoCondition.genericKnightIso`: the full `KnightIso α β Ω` (requires totality of the graph)

## Tags

generic filter, Rasiowa–Sikorski, forcing, knight model, isomorphism
-/

open OrderDual

namespace ModelIsoCondition

variable {α β Ω : Type 0} [Blueprint Ω] [KnightModel α Ω] [KnightModel β Ω]
variable [Encodable α] [Encodable β]
variable [Nonempty α] [Nonempty β]

abbrev DenseIdx := α ⊕ β

private def toCofinalDual (S : Set (ModelIsoCondition α β Ω))
    (hdense : ∀ p : ModelIsoCondition α β Ω, ∃ q ∈ S, q ≤ p) :
    Order.Cofinal (ModelIsoCondition α β Ω)ᵒᵈ where
  carrier := ofDual ⁻¹' S
  isCofinal := fun x => by
    obtain ⟨q, hqS, hqx⟩ := hdense (ofDual x)
    exact ⟨toDual q, hqS, hqx⟩

noncomputable def denseSets : DenseIdx (α := α) (β := β) →
    Order.Cofinal (ModelIsoCondition α β Ω)ᵒᵈ
  | .inl a =>
      toCofinalDual _ (fun p => by
        obtain ⟨q, hqle, hqmem⟩ := inDomain_dense (α := α) (β := β) (Ω := Ω) a p
        exact ⟨q, hqmem, hqle⟩)
  | .inr b =>
      toCofinalDual _ (fun p => by
        obtain ⟨q, hqle, hqmem⟩ := inRange_dense (α := α) (β := β) (Ω := Ω) b p
        exact ⟨q, hqmem, hqle⟩)

noncomputable def genericIdeal : Order.Ideal (ModelIsoCondition α β Ω)ᵒᵈ :=
  Order.idealOfCofinals (toDual (∅ : ModelIsoCondition α β Ω))
    (denseSets (α := α) (β := β) (Ω := Ω))

noncomputable def genericFilter : Set (ModelIsoCondition α β Ω) :=
  ofDual ⁻¹' (genericIdeal (α := α) (β := β) (Ω := Ω) : Set (ModelIsoCondition α β Ω)ᵒᵈ)

lemma mem_genericFilter_empty : (∅ : ModelIsoCondition α β Ω) ∈ genericFilter := by
  change toDual (∅ : ModelIsoCondition α β Ω) ∈ genericIdeal
  exact Order.mem_idealOfCofinals _ _

lemma genericFilter_upward {p q : ModelIsoCondition α β Ω}
    (hp : p ∈ genericFilter) (hpq : p ≤ q) : q ∈ genericFilter :=
  genericIdeal.lower hpq hp

lemma genericFilter_directed {p q : ModelIsoCondition α β Ω}
    (hp : p ∈ genericFilter) (hq : q ∈ genericFilter) :
    ∃ r ∈ genericFilter, r ≤ p ∧ r ≤ q := by
  obtain ⟨r, hr, hrp, hrq⟩ := Order.Ideal.directed genericIdeal p hp q hq
  exact ⟨r, hr, hrp, hrq⟩

lemma genericFilter_meets_inDomain (a : α) :
    ∃ p ∈ genericFilter, p ∈ inDomain (α := α) (β := β) (Ω := Ω) a := by
  obtain ⟨x, hx, hxG⟩ :=
    Order.cofinal_meets_idealOfCofinals (toDual (∅ : ModelIsoCondition α β Ω))
      (denseSets (α := α) (β := β) (Ω := Ω)) (Sum.inl a)
  exact ⟨ofDual x, hxG, hx⟩

lemma genericFilter_meets_inRange (b : β) :
    ∃ p ∈ genericFilter, p ∈ inRange (α := α) (β := β) (Ω := Ω) b := by
  obtain ⟨x, hx, hxG⟩ :=
    Order.cofinal_meets_idealOfCofinals (toDual (∅ : ModelIsoCondition α β Ω))
      (denseSets (α := α) (β := β) (Ω := Ω)) (Sum.inr b)
  exact ⟨ofDual x, hxG, hx⟩

/-! ## Generic Isomorphism -/

/-- Union of graphs of all conditions in the generic filter. -/
noncomputable def genericGraph : Set (α × β) :=
  ⋃ p ∈ (genericFilter (α := α) (β := β) (Ω := Ω)), p.graph

/-- The generic partial Knight isomorphism obtained by taking the union graph over
the generic filter. -/
noncomputable def genericPartialKnightIso : PartialKnightIso α β Ω where
  graph := genericGraph (α := α) (β := β) (Ω := Ω)
  functional := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' haa'
    simp only [genericGraph, Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ :=
      genericFilter_directed (α := α) (β := β) (Ω := Ω) hP hQ
    simp only at haa'
    subst haa'
    exact r.functional _ (hrP hPab) _ (hrQ hQab) rfl
  injective := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' hbb'
    simp only [genericGraph, Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ :=
      genericFilter_directed (α := α) (β := β) (Ω := Ω) hP hQ
    simp only at hbb'
    subst hbb'
    exact r.injective _ (hrP hPab) _ (hrQ hQab) rfl
  order_pres := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' haa'
    simp only [genericGraph, Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ :=
      genericFilter_directed (α := α) (β := β) (Ω := Ω) hP hQ
    exact r.order_pres _ (hrP hPab) _ (hrQ hQab) haa'
  fn_compat := by
    intro n p hp q hq
    simp only [genericGraph, Set.mem_iUnion] at hp hq
    obtain ⟨P, hP, hPp⟩ := hp
    obtain ⟨Q, hQ, hQq⟩ := hq
    obtain ⟨r, hr, hrP, hrQ⟩ :=
      genericFilter_directed (α := α) (β := β) (Ω := Ω) hP hQ
    exact r.fn_compat n p (hrP hPp) q (hrQ hQq)

lemma genericPartialKnightIso_total :
  (genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).toPartialInj.Total := by
  intro a
  obtain ⟨p, hp, hpa⟩ := genericFilter_meets_inDomain (α := α) (β := β) (Ω := Ω) a
  obtain ⟨b, hb⟩ := hpa
  exact ⟨b, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hb⟩⟩⟩

lemma genericPartialKnightIso_symm_total :
  (genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).toPartialInj.symm.Total := by
  intro b
  obtain ⟨p, hp, hpb⟩ := genericFilter_meets_inRange (α := α) (β := β) (Ω := Ω) b
  obtain ⟨a, ha⟩ := hpb
  exact ⟨a, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ha⟩⟩⟩

/-- The global order isomorphism extracted from the generic filter. -/
noncomputable def genericOrderIso : α ≃o β :=
  (genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).toPartialIso.toIso
    (genericPartialKnightIso_total (α := α) (β := β) (Ω := Ω))
    (genericPartialKnightIso_symm_total (α := α) (β := β) (Ω := Ω))

/-- The global Knight isomorphism extracted from the generic filter. -/
noncomputable def genericIso : α ≃ₖ[Ω] β where
  toRelIso := genericOrderIso
  fn_comm := by
    intro n a
    have hPairA :
        (a, genericOrderIso (α := α) (β := β) (Ω := Ω) a) ∈
          (genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).graph := by
      simpa [genericOrderIso, PartialIso.toIso, PartialInj.toFun] using
        (Classical.choose_spec (genericPartialKnightIso_total (α := α) (β := β) (Ω := Ω) a))
    have hPairFn :
        (KnightModel.fn n a, genericOrderIso (α := α) (β := β) (Ω := Ω) (KnightModel.fn n a))
          ∈ (genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).graph := by
      simpa [genericOrderIso, PartialIso.toIso, PartialInj.toFun] using
        (Classical.choose_spec (genericPartialKnightIso_total (α := α) (β := β) (Ω := Ω)
          (KnightModel.fn n a)))
    exact ((genericPartialKnightIso (α := α) (β := β) (Ω := Ω)).fn_compat n
      (a, genericOrderIso (α := α) (β := β) (Ω := Ω) a) hPairA
      (KnightModel.fn n a,
        genericOrderIso (α := α) (β := β) (Ω := Ω) (KnightModel.fn n a)) hPairFn).1 rfl

theorem exists_genericIso : ∃ _f : α ≃ₖ[Ω] β, True :=
  ⟨genericIso (α := α) (β := β) (Ω := Ω), trivial⟩

/-! ## Embedding into a Strict Initial Segment -/

section ExistsEmbedding

variable {K : Type 0} [KnightModel K Ω]

/-- Every countable, nonempty knight model embeds non-surjectively into itself,
by composing a generic isomorphism to a strict initial segment with the inclusion map. -/
lemma exists_embedding_into_strictInitialSegment
    [Countable K] [Nonempty K] :
    ∃ f : K →ₖ[Ω] K, ¬ Function.Surjective f := by
  obtain ⟨a⟩ := ‹Nonempty K›
  obtain ⟨x₀, hx₀⟩ := NoMinOrder.exists_lt a
  haveI hSeg : Nonempty (KnightModel.InitialSegment K a) := ⟨⟨x₀, hx₀⟩⟩
  haveI : Encodable K := Encodable.ofCountable K
  haveI : Encodable (KnightModel.InitialSegment K a) := Encodable.ofCountable _
  let iso : K ≃ₖ[Ω] KnightModel.InitialSegment K a := genericIso
  refine ⟨(KnightModel.initialSegmentInclusion a).comp iso.toKnightEmbedding,
    fun hsurj => ?_⟩
  obtain ⟨x, hx⟩ := hsurj a
  have hlt : (KnightModel.initialSegmentInclusion a).comp iso.toKnightEmbedding x < a := by
    simp only [KnightEmbedding.comp_apply]
    exact (iso.toKnightEmbedding x).2
  exact absurd hx (ne_of_lt hlt)

end ExistsEmbedding

end ModelIsoCondition
