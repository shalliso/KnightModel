import KnightModel.Transfinite.Atlas
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-! # Automatic coherent ladders at the first infinite cardinal

Every strict initial segment below ω₁ has a cofinal subset of order type at
most ω. Such a cofinal subset has no proper nonzero limit points there, so its
closure and coherence requirements hold for any choice of these subsets.
-/

namespace KnightModel.Transfinite

open Ordinal Cardinal Set RankTwo

private theorem no_inner_limit {J : Type} [LinearOrder J] [WellFoundedLT J] {s : Set J}
    (ht : typeLT s ≤ Ordinal.omega0) {d : J} (hd : ∃ z, z < d) (hx : ∃ x : s, d ≤ x) :
    ¬ LadderLimit s d := by
  intro accum
  obtain ⟨x, hdx⟩ := hx
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp ((Ordinal.typein_lt_type LT.lt x).trans_le ht)
  have many (n : ℕ) : ∃ y : s, y.val < d ∧ (n : Ordinal) ≤ Ordinal.typein LT.lt y := by
    induction n with
    | zero =>
      obtain ⟨b, hb⟩ := hd
      obtain ⟨t, ht, _, htd⟩ := accum b hb
      exact ⟨⟨t, ht⟩, htd, by simp⟩
    | succ n ih =>
      obtain ⟨y, hyd, hy⟩ := ih
      obtain ⟨t, hts, hyt, htd⟩ := accum y.val hyd
      have h := (Ordinal.typein_lt_typein LT.lt).2 (show y < (⟨t, hts⟩ : s) from hyt)
      exact ⟨⟨t, hts⟩, htd, Order.succ_le_iff.mpr (hy.trans_lt h)⟩
  obtain ⟨y, hyd, hy⟩ := many k
  have h := (Ordinal.typein_lt_typein LT.lt).2 (show y < x from hyd.trans_le hdx)
  exact (not_lt_of_ge hy) (h.trans_eq hk)

private theorem exists_omega_ladder (b : AtlasIndex ℵ₀) :
    ∃ s : Set (AtlasIndex ℵ₀), (∀ x ∈ s, x < b) ∧
      (∀ g < b, ∃ x ∈ s, g ≤ x) ∧ typeLT s ≤ (ℵ₀ : Cardinal).ord := by
  obtain ⟨s, cofinal, otype⟩ := Ordinal.exists_ord_cof_eq (Iio b)
  let S : Set (AtlasIndex ℵ₀) := {x | ∃ h : x < b, (⟨x, h⟩ : Iio b) ∈ s}
  let e : s ≃o S :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.choose⟩, x.property.choose_spec⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  refine ⟨S, fun _ hx => hx.choose, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, h⟩ := cofinal (⟨g, hg⟩ : Iio b)
    exact ⟨x.val, ⟨x.property, hx⟩, h⟩
  · rw [← e.ordinalType_congr, otype, Cardinal.ord_le_ord]
    apply (Order.cof_le_cardinalMk (Iio b)).trans
    apply Order.lt_succ_iff.mp
    simpa only [AtlasIndex, Cardinal.mk_ord_toType] using Cardinal.mk_Iio_lt b (by simp)

/-- In ZFC the square-ladder premise at ℵ₀ is automatic. -/
theorem squareLadders_aleph0 : Nonempty (SquareLadders (AtlasIndex ℵ₀) (ℵ₀ : Cardinal).ord) := by
  choose S below cof ht using exists_omega_ladder
  have free {b d : AtlasIndex ℵ₀} (hdb : d < b) (hpos : ∃ z, z < d) :
      ¬ LadderLimit (S b) d := by
    obtain ⟨x, hx, hdx⟩ := cof b d hdb
    exact no_inner_limit (by simpa using ht b) hpos ⟨⟨x, hx⟩, hdx⟩
  exact ⟨{
    ladder := S
    below := fun {b x} hx => below b x hx
    cofinal := fun {g b} hgb => cof b g hgb
    closed := fun hdb hpos hlim => (free hdb hpos hlim).elim
    coherent := fun hdb hpos hlim => (free hdb hpos hlim).elim
    orderType_le := ht }⟩

end KnightModel.Transfinite
