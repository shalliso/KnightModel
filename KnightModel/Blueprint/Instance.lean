/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.Basic
import KnightModel.Blueprint.Basic
/-!
# Knight Blueprint Instance for Knight Groups

This file proves that every knight group `K` induces a knight blueprint on the subtype
`{q : ℚ // q ≤ 1}` via the group action.

## Main definitions

* `KnightAutGroup.Blueprint K`: the subtype `{q : ℚ // q ≤ 1}` with multiplication `m * n`
  defined by applying the group element sending `1` to `n` to the value `m`.

## Main results

* `KnightAutGroup.Blueprint.instBlueprint`: every knight group induces a knight blueprint.

## Tags

knight group, knight blueprint, instance
-/

namespace KnightAutGroup

variable (K : KnightAutGroup)

lemma fixes_one_fixes_below {g : K} (hg : g.val 1 = 1) (a : ℚ) (ha : a ≤ 1) :
    g.val a = a :=
  K.fixes_below ha hg

/-- The blueprint of a knight group, defined as `{q : ℚ // q ≤ 1}`. -/
def Blueprint (_K : KnightAutGroup) := {q : ℚ // q ≤ 1}

namespace Blueprint

variable {K : KnightAutGroup}

instance : Inhabited (Blueprint K) :=
  ⟨⟨1, le_rfl⟩⟩

/-- The identity element of the blueprint. -/
def one : Blueprint K := ⟨1, le_rfl⟩

instance : One (Blueprint K) := ⟨one⟩

/-- Multiplication in the blueprint: `m * n` is defined by applying a group element
sending `1` to `n` to the value `m`. -/
noncomputable def mul (m n : Blueprint K) : Blueprint K :=
  ⟨(K.mapTo 1 n.val) m.val, by
    calc (K.mapTo 1 n.val) m.val ≤ (K.mapTo 1 n.val) 1 := by simp [m.property]
      _ = n.val := K.mapTo_spec 1 n.val
      _ ≤ 1 := n.property⟩

noncomputable instance : Mul (Blueprint K) := ⟨mul⟩

lemma one_mul (a : Blueprint K) : 1 * a = a := by
  apply Subtype.ext
  exact K.mapTo_spec 1 a.val

lemma mul_one (a : Blueprint K) : a * 1 = a := by
  apply Subtype.ext
  exact K.fixes_one_fixes_below (K.mapTo_spec 1 1) a.val a.property

lemma mul_right_cancel {a b c : Blueprint K} : a * c = b * c → a = b := by
  intro h
  apply Subtype.ext
  have : (K.mapTo 1 c.val) a.val = (K.mapTo 1 c.val) b.val := by
    calc (K.mapTo 1 c.val) a.val = (a * c).val := rfl
      _ = (b * c).val := congrArg Subtype.val h
      _ = (K.mapTo 1 c.val) b.val := rfl
  exact K.map_injective (K.mapTo 1 c.val) this

lemma mul_assoc (a b c : Blueprint K) : (a * b) * c = a * (b * c) := by
  apply Subtype.ext
  let g_b := K.mapTo 1 b.val
  let g_c := K.mapTo 1 c.val
  let g_bc := K.mapTo 1 (g_c b.val)
  change g_c (g_b a.val) = g_bc a.val
  have hmem : (g_c * g_b : ℚ ≃o ℚ) ∈ K.carrier :=
    K.toSubgroup.mul_mem' g_c.property g_b.property
  let g_comp : K := ⟨g_c * g_b, hmem⟩
  have heq : g_comp a.val = g_bc a.val := by
    apply K.eq_below _ a.val a.property
    show g_comp 1 = g_bc 1
    calc g_comp 1 = (g_c * g_b) 1 := rfl
      _ = g_c (g_b 1) := rfl
      _ = g_c b.val := by rw [K.mapTo_spec]
      _ = g_bc 1 := (K.mapTo_spec 1 (g_c b.val)).symm
  calc g_c (g_b a.val) = g_comp a.val := rfl
    _ = g_bc a.val := heq

noncomputable instance : RightCancelMonoid (Blueprint K) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_right_cancel := fun _ _ _ => mul_right_cancel

instance : LinearOrder (Blueprint K) :=
  Subtype.instLinearOrder _

lemma no_min (a : Blueprint K) : ∃ b : Blueprint K, b < a := by
  obtain ⟨b, hb⟩ := exists_rat_lt a.val
  exact ⟨⟨b, le_trans (le_of_lt hb) a.property⟩, hb⟩

instance : NoMinOrder (Blueprint K) where
  exists_lt := no_min

lemma dense (a b : Blueprint K) (h : a < b) : ∃ c : Blueprint K, a < c ∧ c < b := by
  obtain ⟨c, hac, hcb⟩ := exists_rat_btwn (show a.val < b.val from h)
  exact ⟨⟨c, le_trans (le_of_lt hcb) b.property⟩, hac, hcb⟩

instance : DenselyOrdered (Blueprint K) where
  dense := dense

/-! ### The Knight axioms -/

lemma one_le (a : Blueprint K) : a ≤ 1 := a.property

lemma mul_le (a b : Blueprint K) : a * b ≤ b := by
  change (K.mapTo 1 b.val) a.val ≤ b.val
  calc (K.mapTo 1 b.val) a.val ≤ (K.mapTo 1 b.val) 1 := by simp [a.property]
    _ = b.val := K.mapTo_spec 1 b.val

lemma blueprint_exists_mul_eq (a b : Blueprint K) (h : a ≤ b) :
    ∃ c : Blueprint K, a = c * b := by
  let g := K.mapTo 1 b.val
  have hg_one : g 1 = b.val := K.mapTo_spec 1 b.val
  have hg_inv_b : g.val.symm b.val = 1 := by
    simp [← hg_one]
  have hc_le : g.val.symm a.val ≤ 1 := by
    calc g.val.symm a.val ≤ g.val.symm b.val := g.val.symm.le_iff_le.mpr h
      _ = 1 := hg_inv_b
  use ⟨g.val.symm a.val, hc_le⟩
  apply Subtype.ext
  show a.val = (⟨g.val.symm a.val, hc_le⟩ * b).val
  change a.val = g (g.val.symm a.val)
  simp

lemma exists_mul_eq_right {a b : Blueprint K} (ha : a < 1) (hb : b < 1) :
    ∃ c : Blueprint K, a = b * c := by
  let f := K.mapTo b.val a.val
  have hf : f b.val = a.val := K.mapTo_spec b.val a.val
  by_cases h1 : f 1 ≤ 1
  · use ⟨f 1, h1⟩
    apply Subtype.ext
    change a.val = (K.mapTo 1 (f 1)) b.val
    have heq : f 1 = (K.mapTo 1 (f 1)) 1 := by
      symm
      exact K.mapTo_spec 1 (f 1)
    calc a.val = f b.val := hf.symm
      _ = (K.mapTo 1 (f 1)) b.val := K.eq_below heq b.val (le_of_lt hb)
  · push Not at h1
    have hmax : max a.val b.val < 1 := max_lt ha hb
    obtain ⟨h, hh_mem, hh_fix, hh_squeeze⟩ := K.exists_squeeze hmax h1
    let h' : K := ⟨h, hh_mem⟩
    have hmem : (h' * f : ℚ ≃o ℚ) ∈ K.carrier :=
      K.toSubgroup.mul_mem' h'.property f.property
    let g : K := ⟨h' * f, hmem⟩
    have hg_b : g b.val = a.val := by
      change h' (f b.val) = a.val
      rw [hf]
      exact K.fixes_below (le_max_left a.val b.val) hh_fix
    have hg_1 : g 1 < 1 := by
      change h' (f 1) < 1
      exact hh_squeeze
    use ⟨g 1, le_of_lt hg_1⟩
    apply Subtype.ext
    change a.val = (K.mapTo 1 (g 1)) b.val
    have heq : g 1 = (K.mapTo 1 (g 1)) 1 := by
      symm
      exact K.mapTo_spec 1 (g 1)
    calc a.val = g b.val := hg_b.symm
      _ = (K.mapTo 1 (g 1)) b.val := K.eq_below heq b.val (le_of_lt hb)

instance : Countable (Blueprint K) := Subtype.countable

noncomputable instance instBlueprint : _root_.Blueprint (Blueprint K) where
  one_le := one_le
  mul_le := mul_le
  exists_mul_eq := blueprint_exists_mul_eq
  exists_mul_eq_right := fun _ _ => exists_mul_eq_right

end Blueprint

end KnightAutGroup
