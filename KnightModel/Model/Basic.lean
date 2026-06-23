/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Blueprint.Basic
/-!
# Knight Models

This file defines the `KnightModel` class and establishes its basic theory.

A Knight model is a dense linear order `α` (with no minimum or maximum) equipped with a family
of functions `fn : Ω → α → α` indexed by a `Blueprint Ω`. The functions must:
- respect the blueprint order: `fn n a ≤ fn m a ↔ n ≤ m` (`blueprint_ord`)
- compose as the blueprint multiplication: `fn m (fn n a) = fn (m * n) a` (`blueprint_comp`)
- be surjective onto `(-∞, b]`: for any `a ≤ b` there exists `n` with `fn n b = a` (`capture`)

## Main definitions

* `KnightModel`: the typeclass

## Main results

* `KnightModel.fn_one_eq_id`: `fn 1 = id`
* `KnightModel.dec`: each `fn n` is a retraction — `fn n a ≤ a`
* `KnightModel.ident`: `fn n = id ↔ n = 1`
* `KnightModel.extend`: for `a < b` and any `n`, there exists `c ∈ [a, b]` with `fn n c = a`

## Tags

knight model, blueprint, dense linear order
-/

/-! ## Knight Models -/

/-- A `KnightModel` consists of a dense linear order `α` with a family of functions
`fn : Ω → α → α` indexed by a Knight blueprint `Ω`, where the blueprint's multiplication
determines how the functions compose: `fn m ∘ fn n = fn (m * n)`. -/
class KnightModel (α : Type 0) (Ω : Type 0) [Blueprint Ω] extends
  LinearOrder α, DenselyOrdered α, NoMinOrder α, NoMaxOrder α where
  fn : Ω → α → α
  capture : ∀ a b : α, a ≤ b → ∃ n : Ω, fn n b = a
  blueprint_ord : ∀ m n : Ω, ∀ a : α, fn n a ≤ fn m a ↔ n ≤ m
  blueprint_comp : ∀ m n : Ω, ∀ a : α, fn m (fn n a) = fn (m * n) a

/-! ## Derived lemmas for KnightModel -/

namespace KnightModel

variable {α Ω : Type 0} [Blueprint Ω] [KnightModel α Ω]

/-- `fn 1` is the identity: `fn 1 a = a`. -/
theorem fn_one_eq_id (a : α) : KnightModel.fn (1 : Ω) a = a := by
  obtain ⟨m₀, hm₀⟩ := KnightModel.capture a a le_rfl
  have hidm : KnightModel.fn (m₀ * m₀) a = a := by
    rw [← KnightModel.blueprint_comp, hm₀, hm₀]
  have hinj : ∀ n₁ n₂ : Ω, KnightModel.fn n₁ a = KnightModel.fn n₂ a → n₁ = n₂ :=
    fun n₁ n₂ h => le_antisymm
      ((KnightModel.blueprint_ord n₂ n₁ a).mp (le_of_eq h))
      ((KnightModel.blueprint_ord n₁ n₂ a).mp (le_of_eq h.symm))
  have hm₀_eq : m₀ * m₀ = m₀ := hinj _ _ (hidm.trans hm₀.symm)
  have hm₀_one : m₀ = 1 := mul_right_cancel (hm₀_eq.trans (one_mul m₀).symm)
  rw [← hm₀_one, hm₀]

/-- `fn n` is decreasing: `fn n a ≤ a`. -/
theorem dec (n : Ω) (a : α) : KnightModel.fn n a ≤ a :=
  calc KnightModel.fn n a
      ≤ KnightModel.fn (1 : Ω) a := (KnightModel.blueprint_ord 1 n a).mpr (Blueprint.one_le n)
    _ = a := fn_one_eq_id a

/-- `fn n` is the identity iff `n = 1`. Requires the model to be nonempty. -/
theorem ident [Nonempty α] (n : Ω) : (∀ a : α, KnightModel.fn n a = a) ↔ n = 1 := by
  constructor
  · intro h
    obtain ⟨x⟩ : Nonempty α := inferInstance
    exact le_antisymm (Blueprint.one_le n)
      ((KnightModel.blueprint_ord n 1 x).mp
        (le_of_eq ((fn_one_eq_id x).trans (h x).symm)))
  · rintro rfl
    exact fn_one_eq_id

/-- Extension: for any `n` and `a < b`, there is `c ∈ [a, b]` with `fn n c = a`. -/
theorem extend (n : Ω) (a b : α) (hab : a < b) :
    ∃ c : α, a ≤ c ∧ c ≤ b ∧ KnightModel.fn n c = a := by
  by_cases hn : n = 1
  · exact ⟨a, le_rfl, le_of_lt hab, hn ▸ fn_one_eq_id a⟩
  · have hn_lt : n < 1 := lt_of_le_of_ne (Blueprint.one_le n) hn
    obtain ⟨m, hm⟩ := KnightModel.capture a b (le_of_lt hab)
    have hfn_lt : KnightModel.fn m b < KnightModel.fn (1 : Ω) b := by
      rw [hm, fn_one_eq_id]; exact hab
    have hm_lt : m < 1 :=
      lt_of_le_of_ne
        ((KnightModel.blueprint_ord (1 : Ω) m b).mp (le_of_lt hfn_lt))
        (fun heq => lt_irrefl _ (heq ▸ hfn_lt))
    obtain ⟨d, hd⟩ := Blueprint.exists_right_factor hm_lt hn_lt
    exact ⟨KnightModel.fn d b,
      calc a = KnightModel.fn n (KnightModel.fn d b) := by
              rw [KnightModel.blueprint_comp, ← hd, hm]
          _ ≤ KnightModel.fn (1 : Ω) (KnightModel.fn d b) :=
              (KnightModel.blueprint_ord 1 n _).mpr (Blueprint.one_le n)
          _ = KnightModel.fn d b := fn_one_eq_id _,
      calc KnightModel.fn d b
          ≤ KnightModel.fn (1 : Ω) b :=
              (KnightModel.blueprint_ord 1 d b).mpr (Blueprint.one_le d)
          _ = b := fn_one_eq_id b,
      by rw [KnightModel.blueprint_comp, ← hd, hm]⟩

end KnightModel
