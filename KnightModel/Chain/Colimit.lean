/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Chain.Basic
import Mathlib
/-!
# Knight Chains: Colimit Construction

This file constructs the colimit of a `KnightChain` and proves it is a `KnightModel`.

## Main definitions

* `KnightChain.Colimit`: the colimit (direct limit) type
* `KnightChain.ι`: canonical map `K → c.Colimit` at index `i`
* `KnightChain.colimitFn`: the knight model `fn` action on `c.Colimit`
* `instKnightModelColimit`: `KnightModel` instance for `c.Colimit`
* `KnightChain.isomK`: isomorphism `c.Colimit ≅ K` when `c.dom` is countable
* `KnightChain.inclusion`: embedding of `K` into `c.Colimit` at a given index
* `KnightChain.restrict`: restrict a chain to an initial segment
* `KnightChain.extend`: extend a chain by one step at the top

## Main results

* `KnightChain.not_countable_colimit`: if `c.dom` is uncountable, then `c.Colimit` is uncountable

## Tags

knight chain, colimit, uncountable, directed system
-/

namespace KnightChain

variable {Ω : Type 0} [Blueprint Ω]
variable {K : Type 0} [KnightModel K Ω] [Countable K] [Nonempty K]
variable (c : KnightChain Ω K)

/-- The equivalence relation on `Σ i, K`:
`⟨i, x⟩ ~ ⟨j, y⟩` iff there exists `k ≥ i, j` with `emb_ik x = emb_jk y`.
-/
protected def setoid : _root_.Setoid (Σ _ : c.dom, K) where
  r := fun ⟨i, x⟩ ⟨j, y⟩ ↦ ∃ (k : c.dom) (_ : i ≤ k) (_ : j ≤ k),
    (c.emb i k) x = (c.emb j k) y
  iseqv := {
    refl := fun p => ⟨p.1, le_refl _, le_refl _, rfl⟩
    symm := fun ⟨k, hik, hjk, h⟩ => ⟨k, hjk, hik, h.symm⟩
    trans := by
      intro ⟨i, x⟩ ⟨j, y⟩ ⟨l, z⟩ ⟨k₁, hik₁, hjk₁, h₁⟩ ⟨k₂, hjk₂, hlk₂, h₂⟩
      obtain ⟨k, hk₁k, hk₂k⟩ : ∃ k : c.dom, k₁ ≤ k ∧ k₂ ≤ k
        := IsDirected.directed k₁ k₂
      refine ⟨k, hik₁.trans hk₁k, hlk₂.trans hk₂k, ?_⟩
      have h1 : (c.emb i k) x = (c.emb j k) y := by
        simp only [c.emb_trans hik₁ hk₁k, c.emb_trans hjk₁ hk₁k, Function.comp_apply, h₁]
      have h2 : (c.emb j k) y = (c.emb l k) z := by
        simp only [c.emb_trans hjk₂ hk₂k, c.emb_trans hlk₂ hk₂k, Function.comp_apply, h₂]
      exact h1.trans h2
  }

def Colimit : Type 0 := Quotient c.setoid

def ι (i : c.dom) (x : K) : c.Colimit := Quotient.mk c.setoid ⟨i, x⟩

@[simp]
lemma ι_eq_ι_iff {i j : c.dom} {x : K} {y : K} : c.ι i x = c.ι j y ↔
    ∃ (k : c.dom) (_ : i ≤ k) (_ : j ≤ k),
      (c.emb i k) x = (c.emb j k) y :=
  Quotient.eq (r := c.setoid)

/-- If `(i, x) ~ (j, y)` in the setoid, then for any common upper bound `k` of `i` and `j`,
we have `emb_ik x = emb_jk y`. -/
lemma setoid_emb_eq {i j : c.dom} {x : K} {y : K}
    (h : c.setoid.r ⟨i, x⟩ ⟨j, y⟩) (k : c.dom) (hik : i ≤ k) (hjk : j ≤ k)
    : (c.emb i k) x = (c.emb j k) y := by
  obtain ⟨k₀, hik₀, hjk₀, heq⟩ := h
  obtain ⟨k', hkk', hk₀k'⟩ : ∃ k' : c.dom, k ≤ k' ∧ k₀ ≤ k'
    := IsDirected.directed k k₀
  apply (c.emb k k').injective
  calc (c.emb k k') ((c.emb i k) x)
          = (c.emb i k') x := by rw [c.emb_trans hik hkk']; rfl
        _ = (c.emb j k') y := by
              simp only [c.emb_trans hik₀ hk₀k', c.emb_trans hjk₀ hk₀k', Function.comp_apply, heq]
        _ = (c.emb k k') ((c.emb j k) y) := by rw [c.emb_trans hjk hkk']; rfl

/-! ### Linear order on Colimit -/

/-- The raw `≤` on the sigma type: `(i, x) ≤ (j, y)` iff at some common bound `k`,
`emb_ik x ≤ emb_jk y`. -/
private def rawLE (p q : Σ _ : c.dom, K) : Prop :=
    ∃ (k : c.dom) (_ : p.1 ≤ k) (_ : q.1 ≤ k),
    (c.emb p.1 k) p.2 ≤ (c.emb q.1 k) q.2

/-- `rawLE` is well-defined on setoid classes (left argument). -/
private lemma rawLE_wd_left {p p' q : Σ _i : c.dom, K}
    (hrel : c.setoid.r p p') : c.rawLE p q ↔ c.rawLE p' q := by
  suffices h : ∀ {a b : Σ _ : c.dom, K}, c.setoid.r a b → c.rawLE a q → c.rawLE b q from
    ⟨h hrel, h (c.setoid.iseqv.symm hrel)⟩
  intro a b ⟨k₀, hak₀, hbk₀, heq₀⟩ ⟨k, hak, hqk, hle⟩
  obtain ⟨k'', hkk'', hk₀k''⟩ : ∃ k'' : c.dom, k ≤ k'' ∧ k₀ ≤ k'' := IsDirected.directed k k₀
  refine ⟨k'', hbk₀.trans hk₀k'', hqk.trans hkk'', ?_⟩
  have haeq : (c.emb a.1 k'') a.snd = (c.emb b.1 k'') b.snd :=
    c.setoid_emb_eq ⟨k₀, hak₀, hbk₀, heq₀⟩ k'' (hak.trans hkk'') (hbk₀.trans hk₀k'')
  calc (c.emb b.1 k'') b.snd
      = (c.emb k k'') ((c.emb a.1 k) a.snd) := by
          simp only [← haeq, c.emb_trans hak hkk'', Function.comp_apply]
    _ ≤ (c.emb k k'') ((c.emb q.1 k) q.snd) :=
          (c.emb k k'').toRelEmbedding.map_rel_iff.mpr hle
    _ = (c.emb q.1 k'') q.snd := by
          simp only [c.emb_trans hqk hkk'', Function.comp_apply]

/-- `rawLE` is well-defined on setoid classes (right argument). -/
private lemma rawLE_wd_right {p q q' : Σ _i : c.dom, K}
    (hrel : c.setoid.r q q') : c.rawLE p q ↔ c.rawLE p q' := by
  suffices h : ∀ {a b : Σ _ : c.dom, K}, c.setoid.r a b → c.rawLE p a → c.rawLE p b from
    ⟨h hrel, h (c.setoid.iseqv.symm hrel)⟩
  intro a b ⟨k₀, hak₀, hbk₀, heq₀⟩ ⟨k, hpk, hak, hle⟩
  obtain ⟨k'', hkk'', hk₀k''⟩ : ∃ k'' : c.dom, k ≤ k'' ∧ k₀ ≤ k'' := IsDirected.directed k k₀
  refine ⟨k'', hpk.trans hkk'', hbk₀.trans hk₀k'', ?_⟩
  have haeq : (c.emb a.1 k'') a.snd = (c.emb b.1 k'') b.snd :=
    c.setoid_emb_eq ⟨k₀, hak₀, hbk₀, heq₀⟩ k'' (hak.trans hkk'') (hbk₀.trans hk₀k'')
  calc (c.emb p.1 k'') p.snd
      = (c.emb k k'') ((c.emb p.1 k) p.snd) := by
          simp only [c.emb_trans hpk hkk'', Function.comp_apply]
    _ ≤ (c.emb k k'') ((c.emb a.1 k) a.snd) :=
          (c.emb k k'').toRelEmbedding.map_rel_iff.mpr hle
    _ = (c.emb b.1 k'') b.snd := by
          simp only [← haeq, c.emb_trans hak hkk'', Function.comp_apply]

/-- Define `≤` on the `Colimit` via `Quotient.liftOn₂`. -/
noncomputable instance instLEColimit : LE c.Colimit where
  le a b := Quotient.liftOn₂ a b (c.rawLE) (fun _ _ _ _ hp hq =>
    propext <| (c.rawLE_wd_left hp).trans (c.rawLE_wd_right hq))

/-- Unfolding lemma: `ι i x ≤ ι j y` iff there is a common bound where `emb` makes them
comparable. -/
@[simp]
lemma ι_le_ι_iff {i j : c.dom} {x : K} {y : K} :
    c.ι i x ≤ c.ι j y ↔
    ∃ (k : c.dom) (_ : i ≤ k) (_ : j ≤ k),
    (c.emb i k) x ≤ (c.emb j k) y := Iff.rfl

private lemma le_refl' (a : c.Colimit) : a ≤ a := by
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
  exact ⟨i, le_refl _, le_refl _, le_refl _⟩

private lemma le_trans' {a b d : c.Colimit} (hab : a ≤ b) (hbd : b ≤ d) : a ≤ d := by
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
  obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep b
  obtain ⟨⟨l, z⟩, rfl⟩ := Quotient.exists_rep d
  obtain ⟨k₁, hik₁, hjk₁, hle₁⟩ := hab
  obtain ⟨k₂, hjk₂, hlk₂, hle₂⟩ := hbd
  obtain ⟨k, hk₁k, hk₂k⟩ : ∃ k : c.dom, k₁ ≤ k ∧ k₂ ≤ k
    := IsDirected.directed k₁ k₂
  refine ⟨k, hik₁.trans hk₁k, hlk₂.trans hk₂k, ?_⟩
  calc (c.emb i k) x
      = (c.emb k₁ k) ((c.emb i k₁) x) := by
          rw [c.emb_trans hik₁ hk₁k]; rfl
    _ ≤ (c.emb k₁ k) ((c.emb j k₁) y) :=
          (c.emb k₁ k).toRelEmbedding.map_rel_iff.mpr hle₁
    _ = (c.emb j k) y := by
          rw [c.emb_trans hjk₁ hk₁k]; rfl
    _ = (c.emb k₂ k) ((c.emb j k₂) y) := by
          rw [c.emb_trans hjk₂ hk₂k]; rfl
    _ ≤ (c.emb k₂ k) ((c.emb l k₂) z) :=
          (c.emb k₂ k).toRelEmbedding.map_rel_iff.mpr hle₂
    _ = (c.emb l k) z := by
          rw [c.emb_trans hlk₂ hk₂k]; rfl

private lemma le_antisymm' {a b : c.Colimit} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
  obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep b
  obtain ⟨k₁, hik₁, hjk₁, hxy⟩ := hab
  obtain ⟨k₂, hjk₂, hik₂, hyx⟩ := hba
  obtain ⟨k, hk₁k, hk₂k⟩ : ∃ k : c.dom, k₁ ≤ k ∧ k₂ ≤ k
    := IsDirected.directed k₁ k₂
  apply c.ι_eq_ι_iff.mpr
  refine ⟨k, hik₁.trans hk₁k, hjk₁.trans hk₁k, ?_⟩
  apply le_antisymm
  · calc (c.emb i k) x
        = (c.emb k₁ k) ((c.emb i k₁) x) := by
              rw [c.emb_trans hik₁ hk₁k]; rfl
      _ ≤ (c.emb k₁ k) ((c.emb j k₁) y) :=
              (c.emb k₁ k).toRelEmbedding.map_rel_iff.mpr hxy
      _ = (c.emb j k) y := by
              rw [c.emb_trans hjk₁ hk₁k]; rfl
  · calc (c.emb j k) y
        = (c.emb k₂ k) ((c.emb j k₂) y) := by
              rw [c.emb_trans hjk₂ hk₂k]; rfl
      _ ≤ (c.emb k₂ k) ((c.emb i k₂) x) :=
              (c.emb k₂ k).toRelEmbedding.map_rel_iff.mpr hyx
      _ = (c.emb i k) x := by
              rw [c.emb_trans hik₂ hk₂k]; rfl

private lemma le_total' (a b : c.Colimit) : a ≤ b ∨ b ≤ a := by
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
  obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep b
  obtain ⟨k, hik, hjk⟩ : ∃ k : c.dom, i ≤ k ∧ j ≤ k := IsDirected.directed i j
  rcases le_total ((c.emb i k) x) ((c.emb j k) y) with h | h
  · exact Or.inl ⟨k, hik, hjk, h⟩
  · exact Or.inr ⟨k, hjk, hik, h⟩

/-- The colimit has a `LinearOrder`. -/
noncomputable instance instLinearOrderColimit : LinearOrder c.Colimit where
  le := (instLEColimit c).le
  le_refl := c.le_refl'
  le_trans _ _ _ := c.le_trans'
  le_antisymm _ _ := c.le_antisymm'
  le_total := c.le_total'
  min_def _ _ := rfl
  max_def _ _ := rfl
  toDecidableLE := Classical.decRel _

/-- The colimit is densely ordered: between any two distinct elements, there is a third. -/
noncomputable instance instDenselyOrderedColimit : DenselyOrdered c.Colimit where
  dense := by
    intro a b hlt
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep b
    obtain ⟨k, hik, hjk, hle⟩ := hlt.le
    have hne : (c.emb i k) x ≠ (c.emb j k) y :=
      fun heq => hlt.ne (c.ι_eq_ι_iff.mpr ⟨k, hik, hjk, heq⟩)
    obtain ⟨z, hxz, hzy⟩ := DenselyOrdered.dense _ _ (lt_of_le_of_ne hle hne)
    refine ⟨c.ι k z, ?_, ?_⟩
    · refine ⟨⟨k, hik, le_rfl, by rw [c.emb_rfl]; exact le_of_lt hxz⟩, ?_⟩
      intro ⟨k', hkk', hik', h⟩
      rw [c.emb_trans hik hkk'] at h
      exact absurd ((c.emb k k').toRelEmbedding.map_rel_iff.mp h) (not_le.mpr hxz)
    · refine ⟨⟨k, le_rfl, hjk, by rw [c.emb_rfl]; exact le_of_lt hzy⟩, ?_⟩
      intro ⟨k', hjk', hkk', h⟩
      rw [c.emb_trans hjk hkk'] at h
      exact absurd ((c.emb k k').toRelEmbedding.map_rel_iff.mp h) (not_le.mpr hzy)

/-- The colimit has no minimum element. -/
instance instNoMinOrderColimit : NoMinOrder c.Colimit where
  exists_lt := by
    intro a
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, hyx⟩ := exists_lt x
    refine ⟨c.ι i y, ⟨i, le_rfl, le_rfl, ?_⟩, ?_⟩
    · rw [c.emb_rfl]; exact le_of_lt hyx
    · intro ⟨k, hik, hik', h⟩
      exact absurd ((c.emb i k).toRelEmbedding.map_rel_iff.mp h) (not_le.mpr hyx)

/-- The colimit has no maximum element. -/
instance instNoMaxOrderColimit : NoMaxOrder c.Colimit where
  exists_gt := by
    intro a
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, hxy⟩ := exists_gt x
    refine ⟨c.ι i y, ⟨i, le_rfl, le_rfl, ?_⟩, ?_⟩
    · rw [c.emb_rfl]; exact le_of_lt hxy
    · intro ⟨k, hik, hik', h⟩
      exact absurd ((c.emb i k).toRelEmbedding.map_rel_iff.mp h) (not_le.mpr hxy)

/-! ### The `fn` operation on the Colimit -/

/-- The blueprint action on the colimit: `fn n ⟦(i, x)⟧ = ⟦(i, fn n x)⟧`.
This is well-defined because the embeddings commute with `fn`. -/
noncomputable def colimitFn (n : Ω) : c.Colimit → c.Colimit :=
  Quotient.map (fun ⟨i, x⟩ => ⟨i, KnightModel.fn n x⟩)
    (fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, hik, hjk, heq⟩ => by
      refine ⟨k, hik, hjk, ?_⟩
      calc (c.emb i k) (KnightModel.fn n x)
          = KnightModel.fn n ((c.emb i k) x) := (c.emb i k).fn_comm n x
        _ = KnightModel.fn n ((c.emb j k) y) := by rw [heq]
        _ = (c.emb j k) (KnightModel.fn n y) := ((c.emb j k).fn_comm n y).symm)

@[simp]
lemma colimitFn_mk (n : Ω) (i : c.dom) (x : K) :
    c.colimitFn n (c.ι i x) = c.ι i (KnightModel.fn n x) := rfl

/-! ### KnightModel instance for the Colimit -/

variable [Nonempty c.dom]

/-- The colimit of a chain of Knight models is a Knight model. -/
noncomputable instance instKnightModelColimit : KnightModel c.Colimit Ω where
  fn := c.colimitFn
  capture := by
    intro a b hab
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep b
    obtain ⟨k, hik, hjk, hle⟩ := hab
    obtain ⟨n, hn⟩ := KnightModel.capture ((c.emb i k) x) ((c.emb j k) y) hle
    refine ⟨n, ?_⟩
    change c.ι j (KnightModel.fn n y) = c.ι i x
    exact c.ι_eq_ι_iff.mpr ⟨k, hjk, hik, ((c.emb j k).fn_comm n y).trans hn⟩
  blueprint_ord := by
    intro m n a
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    change c.ι i (KnightModel.fn n x) ≤ c.ι i (KnightModel.fn m x) ↔ n ≤ m
    constructor
    · intro ⟨k, hik, hik', hle⟩
      simp only [KnightEmbedding.map_fn] at hle
      exact (KnightModel.blueprint_ord m n ((c.emb i k) x)).mp hle
    · intro hn
      exact ⟨i, le_rfl, le_rfl, by
        rw [c.emb_rfl]; exact (KnightModel.blueprint_ord m n x).mpr hn⟩
  blueprint_comp := by
    intro m n a
    obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep a
    change c.ι i (KnightModel.fn m (KnightModel.fn n x)) =
      c.ι i (KnightModel.fn (m * n) x)
    congr 1
    exact KnightModel.blueprint_comp m n x

noncomputable instance : Encodable K :=
  (nonempty_encodable K).some

instance [Countable c.dom] : Countable c.Colimit :=
  inferInstanceAs (Countable (Quotient c.setoid))

noncomputable instance [Countable c.dom] : Encodable c.Colimit :=
  (nonempty_encodable c.Colimit).some

instance : Nonempty c.Colimit :=
  ⟨c.ι (Nonempty.some inferInstance) (Nonempty.some inferInstance)⟩

noncomputable def isomK [Countable c.dom]
    : c.Colimit ≃ₖ[Ω] K :=
  ModelIsoCondition.genericIso

/-! ### Inclusion embeddings -/

/-- The canonical embedding of `K` at stage `i` into the colimit of the chain. -/
noncomputable def inclusion (i : c.dom) : K →ₖ[Ω] c.Colimit where
  toRelEmbedding := {
    toFun := c.ι i
    inj' := by
      intro x y hxy
      obtain ⟨k, _, _, heq⟩ := c.ι_eq_ι_iff.mp hxy
      exact (c.emb i k).injective heq
    map_rel_iff' := by
      intro x y
      constructor
      · intro ⟨k, hik, hik', hle⟩
        exact (c.emb i k).toRelEmbedding.map_rel_iff.mp hle
      · intro hle
        exact ⟨i, le_rfl, le_rfl, by rw [c.emb_rfl]; exact hle⟩
  }
  fn_comm := by
    intro n x
    rfl

/-! ### Coherence lemma -/

omit [Nonempty c.dom] in
/-- The inclusion of stage `i` equals the inclusion of stage `j` composed with `emb i j`. -/
lemma inclusion_comp_emb {i j : c.dom} (hij : i ≤ j) :
    c.inclusion i = (c.inclusion j) ∘ (c.emb i j) := by
  ext x
  change c.ι i x = c.ι j ((c.emb i j) x)
  exact c.ι_eq_ι_iff.mpr ⟨j, hij, le_refl _, by rw [c.emb_rfl]; rfl⟩

/-! ### extend -/

/-- Extend a chain of countable length by one step: add a new index `α` at the top (so the
domain grows from `Set.Iio α` to `Set.Iic α`). -/
noncomputable def extend (α : Omega1) (hdom : c.dom = Set.Iio α)
    [Countable c.dom]
    : KnightChain Ω K where
  dom := Set.Iic α
  dom_initial _x hx _y hy := (hy.trans_le hx).le
  emb i j :=
    if hi : i.val < α then
      if hj : j.val < α then
        -- Both old indices: use the existing chain's emb
        c.emb ⟨i.val, hdom ▸ hi⟩ ⟨j.val, hdom ▸ hj⟩
      else
        -- i < α = j (the new top): embKNontrivial ∘ isomK ∘ inclusion i
        -- (i witnesses that c.dom is nonempty)
        haveI : Nonempty c.dom := ⟨⟨i.val, hdom ▸ hi⟩⟩
        KnightEmbedding.comp embKNontrivial
          (KnightEmbedding.comp (KnightIso.toKnightEmbedding c.isomK)
            (c.inclusion ⟨i.val, hdom ▸ hi⟩))
    else
      -- i = α (= j, since i ≤ j ≤ α and ¬ i < α): identity
      KnightEmbedding.id
  emb_rfl i := by
    rcases lt_or_eq_of_le (Set.mem_Iic.mp i.property) with hi | hi
    · simp only [dif_pos hi]
      exact c.emb_rfl ⟨i.val, hdom ▸ hi⟩
    · simp only [dif_neg (not_lt.mpr hi.symm.le)]
  emb_trans {i} {j} {k} hij hjk := by
    -- Case split on whether k < α or k = α
    rcases lt_or_eq_of_le (Set.mem_Iic.mp k.property) with hk | hk
    · -- k < α: then j < α and i < α
      have hj : j.val < α := (Subtype.coe_le_coe.mpr hjk).trans_lt hk
      have hi : i.val < α := (Subtype.coe_le_coe.mpr hij).trans_lt hj
      simp only [dif_pos hi, dif_pos hj, dif_pos hk]
      exact c.emb_trans hij hjk
    · -- k = α
      rcases lt_or_eq_of_le (Set.mem_Iic.mp i.property) with hi | hi
      · rcases lt_or_eq_of_le (Set.mem_Iic.mp j.property) with hj | hj
        · -- i < α, j < α, k = α
          haveI : Nonempty c.dom := ⟨⟨i.val, hdom ▸ hi⟩⟩
          simp only [dif_pos hi, dif_pos hj, dif_neg (not_lt.mpr hk.symm.le)]
          -- Goal: embK ∘ isomK ∘ incl i = (embK ∘ isomK ∘ incl j) ∘ c.emb i j
          funext x
          simp only [KnightEmbedding.comp_apply, Function.comp_apply]
          rw [c.inclusion_comp_emb (show (⟨i.val, hdom ▸ hi⟩ : c.dom) ≤
            ⟨j.val, hdom ▸ hj⟩ from hij)]
          rfl
        · -- i < α, j = α = k
          simp only [dif_pos hi, dif_neg (not_lt.mpr hk.symm.le),
            dif_neg (not_lt.mpr hj.symm.le)]
          ext x; simp [KnightEmbedding.id_apply]
      · -- i = α = j = k
        have hj_neg : ¬ j.val < α := not_lt.mpr (hi.ge.trans (Subtype.coe_le_coe.mpr hij))
        simp only [dif_neg (not_lt.mpr hi.symm.le), dif_neg hj_neg]
        ext x; simp [KnightEmbedding.id_apply]
  emb_range_in_nontrivial {i} {j} hij x := by
    rcases lt_or_eq_of_le (Set.mem_Iic.mp i.property) with hi | hi
    · rcases lt_or_eq_of_le (Set.mem_Iic.mp j.property) with hj | hj
      · -- i < α and j < α: use c.emb_range_in_nontrivial
        simp only [dif_pos hi, dif_pos hj]
        exact c.emb_range_in_nontrivial hij x
      · -- i < α, j = α: the emb is embKNontrivial ∘ isomK ∘ inclusion i
        haveI : Nonempty c.dom := ⟨⟨i.val, hdom ▸ hi⟩⟩
        simp only [dif_pos hi, dif_neg (not_lt.mpr hj.symm.le)]
        exact ⟨(KnightIso.toKnightEmbedding c.isomK) (c.ι ⟨i.val, hdom ▸ hi⟩ x), rfl⟩
    · -- i = α: contradiction
      exact absurd (Subtype.coe_lt_coe.mpr hij) (not_lt.mpr (j.property.trans hi.symm.le))

/-! ### Uncountability -/

omit [Nonempty c.dom] in
theorem not_countable_colimit
    (hdom : ¬ Countable c.dom) : ¬ Countable c.Colimit := by
  intro hColimit
  haveI := hColimit
  apply hdom
  -- Pick x₀ not in the range of embKNontrivial
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : K, ∀ y : K, embKNontrivial (Ω := Ω) y ≠ x₀ := by
    have h := embKNontrivial_not_surjective (Ω := Ω) (K := K)
    simp only [Function.Surjective] at h
    push Not at h; exact h
  -- The map i ↦ c.ι i x₀ is injective
  have hinj : Function.Injective (fun i : c.dom => c.ι i x₀) := by
    intro i j heq
    obtain ⟨k, hik, hjk, hk⟩ := c.ι_eq_ι_iff.mp heq
    rcases le_total i j with hij | hji
    · -- i ≤ j ≤ k: use emb i k = emb j k ∘ emb i j to get emb i j x₀ = x₀
      have step1 : c.emb i k x₀ = c.emb j k (c.emb i j x₀) := by
        rw [c.emb_trans hij hjk]; rfl
      have step2 : c.emb i j x₀ = x₀ :=
        (c.emb j k).injective (step1.symm.trans hk)
      rcases eq_or_lt_of_le hij with rfl | hlt
      · rfl
      · obtain ⟨y, hy⟩ := c.emb_range_in_nontrivial hlt x₀
        exact absurd (hy.symm.trans step2) (hx₀ y)
    · -- j ≤ i ≤ k: symmetric
      have step1 : c.emb j k x₀ = c.emb i k (c.emb j i x₀) := by
        rw [c.emb_trans hji hik]; rfl
      have step2 : c.emb j i x₀ = x₀ :=
        (c.emb i k).injective (step1.symm.trans hk.symm)
      rcases eq_or_lt_of_le hji with rfl | hlt
      · rfl
      · obtain ⟨y, hy⟩ := c.emb_range_in_nontrivial hlt x₀
        exact absurd (hy.symm.trans step2) (hx₀ y)
  exact hinj.countable

end KnightChain
