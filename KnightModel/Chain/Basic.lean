/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.GenericFilter
import Mathlib
/-!
# Knight Chains: Basic Definitions

This file defines `KnightChain` and its core components.

## Main definitions

* `Omega1`: abbreviation for `(Cardinal.aleph 1).ord.ToType`
* `KnightChain`: directed system of embeddings with initial-segment domain; every transition
  embedding factors through `embKNontrivial`
* `KnightChain.embKNontrivial`: a fixed non-surjective self-embedding of a countable knight model

## Tags

knight chain, directed system, omega1
-/

/-- The type of countable ordinals, i.e. ordinals strictly below ω₁. -/
abbrev Omega1 := (Cardinal.aleph 1).ord.ToType

noncomputable instance : Nonempty Omega1 :=
  Ordinal.nonempty_toType_iff.mpr
    (fun h => absurd (Cardinal.ord_eq_zero.mp h) (Cardinal.aleph_pos _).ne')

instance : WellFoundedLT Omega1 := inferInstance

namespace KnightChain

variable {Ω : Type 0} [Blueprint Ω] {K : Type 0} [KnightModel K Ω] [Countable K] [Nonempty K]

/-- A non-surjective self-embedding of K, used to ensure extend adds new elements. -/
noncomputable def embKNontrivial : K →ₖ[Ω] K :=
  ModelIsoCondition.exists_embedding_into_strictInitialSegment.choose

lemma embKNontrivial_not_surjective :
    ¬ Function.Surjective (embKNontrivial (Ω := Ω) (K := K) : K → K) :=
  ModelIsoCondition.exists_embedding_into_strictInitialSegment.choose_spec

end KnightChain

structure KnightChain (Ω : Type 0) [Blueprint Ω]
    (K : Type 0) [KnightModel K Ω] [Countable K] [Nonempty K] : Type 0
    where
  /-- The active initial segment of ω₁ indexing this chain. -/
  dom : Set Omega1
  /-- `dom` is an initial segment: if `x ∈ dom` and `y < x` then `y ∈ dom`. -/
  dom_initial : ∀ x ∈ dom, ∀ y < x, y ∈ dom
  emb : dom → dom → K →ₖ[Ω] K
  emb_rfl : ∀ (i : dom), emb i i = KnightEmbedding.id
  emb_trans : ∀ {i j k : dom},
    i ≤ j → j ≤ k → emb i k = (emb j k) ∘ (emb i j)
  /-- Every transition embedding has range contained in `range embKNontrivial`. -/
  emb_range_in_nontrivial : ∀ {i j : dom}, i < j → ∀ x : K,
    ∃ y : K, emb i j x = KnightChain.embKNontrivial (Ω := Ω) (K := K) y
