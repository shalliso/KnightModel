/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import Mathlib

namespace KnightModel.StatementAudit

class Blueprint (Ω : Type 0) extends
    RightCancelMonoid Ω, LinearOrder Ω, DenselyOrdered Ω, NoMinOrder Ω, Countable Ω where
  one_le : ∀ a : Ω, a ≤ 1
  mul_le : ∀ a b : Ω, a * b ≤ b
  exists_mul_eq : ∀ a b : Ω, a ≤ b → ∃ c : Ω, a = c * b
  exists_mul_eq_right : ∀ a b : Ω, a < 1 → b < 1 → ∃ c : Ω, a = b * c

class KnightModel (α : Type 0) (Ω : Type 0) [Blueprint Ω] extends
    LinearOrder α, DenselyOrdered α, NoMinOrder α, NoMaxOrder α where
  fn : Ω → α → α
  capture : ∀ a b : α, a ≤ b → ∃ n : Ω, fn n b = a
  blueprint_ord : ∀ m n : Ω, ∀ a : α, fn n a ≤ fn m a ↔ n ≤ m
  blueprint_comp : ∀ m n : Ω, ∀ a : α, fn m (fn n a) = fn (m * n) a

structure KnightIso (α β Ω : Type 0) [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] extends α ≃o β where
  fn_comm : ∀ n : Ω, ∀ a : α,
    toFun (KnightModel.fn n a) = KnightModel.fn n (toFun a)

theorem exists_blueprint : ∃ (Ω : Type 0), Nonempty (Blueprint Ω) := by
  sorry

theorem nonempty_knightIso_of_encodable {Ω : Type 0} [Blueprint Ω]
    {α β : Type 0} [KnightModel α Ω] [KnightModel β Ω]
    [Encodable α] [Encodable β] [Nonempty α] [Nonempty β] :
    Nonempty (KnightIso α β Ω) := by
  sorry

open Cardinal in
theorem knightModel_card_le_aleph_one {Ω : Type 0} [Blueprint Ω]
    {α : Type 0} [KnightModel α Ω] : #α ≤ aleph 1 := by
  sorry

open Cardinal in
theorem exists_aleph_one_model {Ω : Type 0} [Blueprint Ω] :
    ∃ (α : Type 0) (_ : KnightModel α Ω), #α = aleph 1 := by
  sorry

end KnightModel.StatementAudit
