/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Aleph1
import KnightModel.Blueprint.Instance
import KnightModel.KnightAutGroup.Instance
/-!
# Main Results

This file states and proves the two central theorems of the KnightModel project, which
generalizes results from the paper:

Knight JF. A complete Lω1ω-sentence characterizing ℵ1. Journal of Symbolic Logic. 1977;42(1):59-62.
doi:10.2307/2272318

## Definitions

A **blueprint** (`KnightModel/Blueprint/Basic.lean`) is a type `Ω` satisfying:

```
class Blueprint (Ω : Type 0) extends
    RightCancelMonoid Ω, LinearOrder Ω, DenselyOrdered Ω, NoMinOrder Ω, Countable Ω where
  one_le : ∀ a : Ω, a ≤ 1
  mul_le : ∀ a b : Ω, a * b ≤ b
  exists_mul_eq : ∀ a b : Ω, a ≤ b → ∃ c : Ω, a = c * b
  exists_mul_eq_right : ∀ a b : Ω, a < 1 → b < 1 → ∃ c : Ω, a = b * c
```

A **knight model** (`KnightModel/Model/Basic.lean`) is a type `α` acted on by a blueprint `Ω`:

```
class KnightModel (α : Type 0) (Ω : Type 0) [Blueprint Ω] extends
    LinearOrder α, DenselyOrdered α, NoMinOrder α, NoMaxOrder α where
  fn : Ω → α → α
  capture : ∀ a b : α, a ≤ b → ∃ n : Ω, fn n b = a
  blueprint_ord : ∀ m n : Ω, ∀ a : α, fn n a ≤ fn m a ↔ n ≤ m
  blueprint_comp : ∀ m n : Ω, ∀ a : α, fn m (fn n a) = fn (m * n) a
```

Think of the blueprint as encoding the Lω1ω-theory of a Knight model.

## Main results

* `knightModel_card_le_aleph_one`: every Knight model has cardinality `#α ≤ ℵ₁`
* `exists_aleph_one_model`: for every blueprint there exists a Knight model with `#α = ℵ₁`
* `nonempty_knightIso_of_encodable`: any two countable nonempty Knight models of the same blueprint
  are isomorphic
* `exists_blueprint`: a blueprint exists (so no theorem above is vacuous)

## Tags

knight model, blueprint, cardinality, aleph one
-/

/-- A blueprint exists: `{q : ℚ // q ≤ 1}` with the action of a knight automorphism group
is a blueprint. -/
theorem exists_blueprint : ∃ (Ω : Type 0), Nonempty (Blueprint Ω) :=
  ⟨KnightAutGroup.Blueprint knightAutGroup, ⟨inferInstance⟩⟩

open Cardinal in
/-- Every Knight model has cardinality at most ℵ₁. -/
theorem knightModel_card_le_aleph_one {Ω : Type 0} [Blueprint Ω]
    {α : Type 0} [KnightModel α Ω] : #α ≤ aleph 1 :=
  KnightModel.knightModel_card_le_aleph_one (Ω := Ω)

open Cardinal in
/-- For every blueprint, there exists a Knight model of cardinality exactly ℵ₁. -/
theorem exists_aleph_one_model {Ω : Type 0} [Blueprint Ω] :
    ∃ (α : Type 0) (_ : KnightModel α Ω), #α = aleph 1 :=
  KnightModel.exists_aleph_one_model (Ω := Ω)

/-- Any two countable nonempty Knight models of the same blueprint are isomorphic. -/
theorem nonempty_knightIso_of_encodable {Ω : Type 0} [Blueprint Ω]
    {α β : Type 0} [KnightModel α Ω] [KnightModel β Ω]
    [Encodable α] [Encodable β] [Nonempty α] [Nonempty β] :
    Nonempty (α ≃ₖ[Ω] β) :=
  ⟨ModelIsoCondition.genericIso⟩
