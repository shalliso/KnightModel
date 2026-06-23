/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Cardinality
import KnightModel.Chain.Zorn
/-!
# Main Cardinality Theorem for Knight Models

This file states and proves the main cardinality result for Knight models:
for every Knight blueprint, there exists a Knight model of cardinality **exactly ℵ₁**.

## Main result

* `KnightModel.exists_aleph_one_model`: for every `Blueprint Ω`, there exists a
  `KnightModel α Ω` with `#α = ℵ₁`.

## Background

The proof combines two results:
* Every Knight model has cardinality at most ℵ₁ (`knightModel_card_le_aleph_one`,
  proved in `Cardinality.lean` via a cofinal ω₁-sequence argument).
* For every blueprint there exists an **uncountable** Knight model
  (`KnightChain.exists_uncountable_knightModel`, proved in `KnightChain.lean` via a
  Zorn's lemma construction of an ω₁-length directed system).

Together these pin down the cardinality to exactly ℵ₁.

## Tags

knight model, cardinality, aleph one
-/

open Cardinal

namespace KnightModel

/-- **Main theorem**: for every Knight blueprint Ω, there exists a Knight model of
cardinality exactly ℵ₁. The bound `#α ≤ ℵ₁` is sharp: every Knight model satisfies it
(see `knightModel_card_le_aleph_one`), and this theorem shows it is achieved. -/
theorem exists_aleph_one_model {Ω : Type 0} [Blueprint Ω] :
    ∃ (α : Type 0) (_ : KnightModel α Ω), #α = aleph 1 := by
  obtain ⟨α, ⟨hmodel⟩, huncountable⟩ :=
    KnightChain.exists_uncountable_knightModel (Ω := Ω)
  haveI := hmodel
  refine ⟨α, hmodel, le_antisymm (knightModel_card_le_aleph_one (Ω := Ω) (α := α)) ?_⟩
  -- Goal: aleph 1 ≤ #α
  -- Strategy: show #α < aleph 1, which contradicts the goal and huncountable
  by_contra h
  push Not at h
  -- Now h : #α < aleph 1
  -- And huncountable : ¬Countable α
  -- These two facts together should lead to a contradiction via the new lemmas
  have h1 : #α ≤ aleph0 := Cardinal.lt_aleph_one_iff.mp h
  have h2 : Countable α := Cardinal.mk_le_aleph0_iff.mp h1
  exact huncountable h2

end KnightModel
