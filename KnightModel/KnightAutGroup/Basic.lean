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
# Knight Aut Groups

This file defines knight aut groups and establishes their basic theory.

A **knight aut group** is a subgroup `K ≤ Aut(ℚ, ≤)` satisfying three axioms:

- `transitivity`: `K` acts transitively on `ℚ` — for any `a b : ℚ` there exists `g ∈ K` with
  `g a = b`
- `fixing`: the action is "supported below fixed points" — if `g ∈ K` fixes `b` and `a ≤ b`,
  then `g` fixes `a`
- `density`: for any `a < b < c` there exists `g ∈ K` fixing `a` with `g c < b`

## Main definitions

* `KnightAutGroup`: the structure, extending `Subgroup (ℚ ≃o ℚ)` with the three axioms
* `KnightAutGroup.mapTo`: noncomputable choice of a group element mapping `a` to `b`

## Main results

* `KnightAutGroup.fixes_below`: if `g` fixes `b` and `a ≤ b` then `g` fixes `a`
* `KnightAutGroup.exists_squeeze`: density axiom in explicit form
* `KnightAutGroup.eq_below`: if `g b = h b` then `g a = h a` for all `a ≤ b`
* `KnightAutGroup.map_mono`: `g` is order-preserving (`a ≤ b ↔ g a ≤ g b`)
* `KnightAutGroup.map_strictMono`: `g` is strictly order-preserving (`a < b ↔ g a < g b`)

## Tags

knight group, order automorphism, rational numbers
-/

/-! ## Knight Aut Groups -/

/-- A `KnightAutGroup` is a subgroup of the order-automorphism group `ℚ ≃o ℚ` satisfying three
axioms: transitivity (the group acts transitively on `ℚ`), fixing (any element fixing `b` also
fixes everything below `b`), and density (for `a < b < c` some element fixes `a` and moves `c`
below `b`). -/
structure KnightAutGroup extends Subgroup (ℚ ≃o ℚ) where
  transitivity : ∀ a b : ℚ, ∃ g ∈ carrier, g a = b
  fixing : ∀ a b : ℚ, a ≤ b → ∀ g ∈ carrier, g b = b → g a = a
  density : ∀ a b c : ℚ, a < b → b < c → ∃ g ∈ carrier, g a = a ∧ g c < b

/-! ## Instances and coercions -/

instance : SetLike KnightAutGroup (ℚ ≃o ℚ) where
  coe s := s.toSubgroup.carrier
  coe_injective p q h := by
    cases p
    cases q
    congr
    exact SetLike.coe_injective h

instance : SubgroupClass KnightAutGroup (ℚ ≃o ℚ) where
  mul_mem {G} := G.toSubgroup.mul_mem'
  one_mem {G} := G.toSubgroup.one_mem'
  inv_mem {G} := G.toSubgroup.inv_mem'

instance {K : KnightAutGroup} : CoeFun K (fun _ => ℚ → ℚ) where
  coe g := g.val

/-! ## Derived lemmas for KnightAutGroup -/

namespace KnightAutGroup

variable {K : KnightAutGroup}

lemma exists_map (a b : ℚ) : ∃ g ∈ K.carrier, g a = b :=
  K.transitivity a b

/-- A noncomputable choice of group element mapping `a` to `b`. -/
noncomputable def mapTo (a b : ℚ) : K :=
  ⟨(K.exists_map a b).choose, (K.exists_map a b).choose_spec.1⟩

lemma mapTo_spec (a b : ℚ) : (K.mapTo a b) a = b :=
  (K.exists_map a b).choose_spec.2

lemma fixes_below {a b : ℚ} (hab : a ≤ b) {g : K} (hgb : g b = b) : g a = a :=
  K.fixing a b hab g g.property hgb

lemma exists_squeeze {a b c : ℚ} (hab : a < b) (hbc : b < c) :
    ∃ g ∈ K.carrier, g a = a ∧ g c < b :=
  K.density a b c hab hbc

lemma eq_below {g h : K} {b : ℚ} (heq : g b = h b) :
    ∀ a ≤ b, g a = h a := by
  intro a hab
  have : (h⁻¹ * g) a = a := fixes_below hab (by simp [heq])
  simpa using congrArg h this

@[simp]
lemma map_mono {g : K} {a b : ℚ} : a ≤ b ↔ g a ≤ g b :=
  g.val.le_iff_le.symm

@[simp]
lemma map_strictMono {g : K} {a b : ℚ} : a < b ↔ g a < g b :=
  g.val.lt_iff_lt.symm

lemma map_injective (g : K) : Function.Injective g :=
  g.val.injective

lemma map_surjective (g : K) : Function.Surjective g :=
  g.val.surjective

end KnightAutGroup
