/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.End
import Mathlib.Data.Rat.Encodable
/-!
# Knight Blueprints

This file defines the `Blueprint` typeclass and establishes its basic theory.

A **blueprint** is a countable right-cancellative monoid `Ω` equipped with a compatible dense
linear order, in which `1` is the maximum element and multiplication is order-decreasing. The
four axioms are:

- `one_le`: `1` is the maximum element (`a ≤ 1` for all `a`)
- `mul_le`: multiplication decreases the right factor (`a * b ≤ b`)
- `exists_mul_eq`: if `a ≤ b` then `a = c * b` for some `c` (left-divisibility below `b`)
- `exists_mul_eq_right`: if `a, b < 1` then `a = b * c` for some `c` (right-divisibility
  among proper elements)

## Main definitions

* `Blueprint`: the typeclass

## Main results

* `Blueprint.le_one`: every element satisfies `a ≤ 1`
* `Blueprint.mul_le_right`: `a * b ≤ b`
* `Blueprint.exists_left_factor`: if `a ≤ b` then `∃ c, a = c * b`
* `Blueprint.exists_right_factor`: if `a, b < 1` then `∃ c, a = b * c`
* `Blueprint.mul_le_mul_right`: `a ≤ b → a * c ≤ b * c`

## Tags

knight blueprint, right-cancel monoid, dense linear order
-/

/-! ## Knight Blueprints -/

/-- A `Blueprint` is a countable right-cancellative monoid `Ω` with a compatible dense linear
order in which `1` is the maximum element. Multiplication is order-decreasing (`a * b ≤ b`), and
the order is characterised by divisibility: `a ≤ b` iff `b` left-divides `a` (`a = c * b` for
some `c`), and any two proper elements are right-comparable (`a = b * c` for some `c`). -/
class Blueprint (Ω : Type 0) extends
  RightCancelMonoid Ω, LinearOrder Ω, DenselyOrdered Ω, NoMinOrder Ω, Countable Ω where
  one_le : ∀ a : Ω, a ≤ 1
  mul_le : ∀ a b : Ω, a * b ≤ b
  exists_mul_eq : ∀ a b : Ω, a ≤ b → ∃ c : Ω, a = c * b
  exists_mul_eq_right : ∀ a b : Ω, a < 1 → b < 1 → ∃ c : Ω, a = b * c

/-! ## Derived lemmas for Blueprint -/

namespace Blueprint

variable {Ω : Type 0} [Blueprint Ω]

@[simp]
lemma le_one (a : Ω) : a ≤ 1 :=
  Blueprint.one_le a

lemma mul_le_right (a b : Ω) : a * b ≤ b :=
  Blueprint.mul_le a b

lemma exists_left_factor {a b : Ω} (h : a ≤ b) : ∃ c : Ω, a = c * b :=
  Blueprint.exists_mul_eq a b h

lemma exists_right_factor {a b : Ω} (ha : a < 1) (hb : b < 1) : ∃ c : Ω, a = b * c :=
  Blueprint.exists_mul_eq_right a b ha hb

lemma mul_le_mul_right {a b : Ω} (c : Ω) (h : a ≤ b) : a * c ≤ b * c := by
  obtain ⟨d, hd⟩ := exists_left_factor h
  rw [hd]
  calc d * b * c = d * (b * c) := mul_assoc d b c -- or _ _ _
       _         ≤ b * c       := mul_le_right d (b * c) -- or _ _

end Blueprint
