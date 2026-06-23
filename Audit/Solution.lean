/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import Mathlib
import KnightModel.Model.Aleph1
import KnightModel.Blueprint.Instance
import KnightModel.KnightAutGroup.Instance

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

@[reducible]
instance toStatementAuditBlueprint {Ω : Type 0} [inst : _root_.Blueprint Ω] : Blueprint Ω :=
  { inst.toRightCancelMonoid, inst.toLinearOrder, inst.toDenselyOrdered,
    inst.toNoMinOrder, inst.toCountable with
    one_le := inst.one_le
    mul_le := inst.mul_le
    exists_mul_eq := inst.exists_mul_eq
    exists_mul_eq_right := inst.exists_mul_eq_right }

@[reducible]
instance toKnightModelBlueprint {Ω : Type 0} [inst : Blueprint Ω] : _root_.Blueprint Ω :=
  { inst.toRightCancelMonoid, inst.toLinearOrder, inst.toDenselyOrdered,
    inst.toNoMinOrder, inst.toCountable with
    one_le := inst.one_le
    mul_le := inst.mul_le
    exists_mul_eq := inst.exists_mul_eq
    exists_mul_eq_right := inst.exists_mul_eq_right }

@[reducible]
instance toStatementAuditKnightModel {α Ω : Type 0} [Blueprint Ω]
    [km : _root_.KnightModel α Ω] : KnightModel α Ω :=
  { km.toLinearOrder, km.toDenselyOrdered, km.toNoMinOrder, km.toNoMaxOrder with
    fn := km.fn
    capture := km.capture
    blueprint_ord := km.blueprint_ord
    blueprint_comp := km.blueprint_comp }

@[reducible]
instance toRootKnightModel {α Ω : Type 0} [Blueprint Ω]
    [km : KnightModel α Ω] : _root_.KnightModel α Ω :=
  { km.toLinearOrder, km.toDenselyOrdered, km.toNoMinOrder, km.toNoMaxOrder with
    fn := km.fn
    capture := km.capture
    blueprint_ord := km.blueprint_ord
    blueprint_comp := km.blueprint_comp }

theorem exists_blueprint : ∃ (Ω : Type 0), Nonempty (Blueprint Ω) := by
  haveI : _root_.Blueprint (KnightAutGroup.Blueprint knightAutGroup) :=
    KnightAutGroup.Blueprint.instBlueprint
  exact ⟨KnightAutGroup.Blueprint knightAutGroup, ⟨inferInstance⟩⟩

theorem nonempty_knightIso_of_encodable {Ω : Type 0} [Blueprint Ω]
    {α β : Type 0} [KnightModel α Ω] [KnightModel β Ω]
    [Encodable α] [Encodable β] [Nonempty α] [Nonempty β] :
    Nonempty (KnightIso α β Ω) := by
  letI : _root_.Blueprint Ω := toKnightModelBlueprint
  letI : _root_.KnightModel α Ω := toRootKnightModel
  letI : _root_.KnightModel β Ω := toRootKnightModel
  have f : α ≃ₖ[Ω] β := ModelIsoCondition.genericIso
  exact ⟨⟨f.toRelIso, f.fn_comm⟩⟩

open Cardinal in
theorem knightModel_card_le_aleph_one {Ω : Type 0} [Blueprint Ω]
    {α : Type 0} [KnightModel α Ω] : #α ≤ aleph 1 := by
  letI : _root_.Blueprint Ω := toKnightModelBlueprint
  letI : _root_.KnightModel α Ω := toRootKnightModel
  exact _root_.KnightModel.knightModel_card_le_aleph_one (Ω := Ω)

open Cardinal in
theorem exists_aleph_one_model {Ω : Type 0} [Blueprint Ω] :
    ∃ (α : Type 0) (_ : KnightModel α Ω), #α = aleph 1 := by
  letI : _root_.Blueprint Ω := toKnightModelBlueprint
  obtain ⟨α, hm, hcard⟩ := _root_.KnightModel.exists_aleph_one_model (Ω := Ω)
  exact ⟨α, toStatementAuditKnightModel, hcard⟩

end KnightModel.StatementAudit
