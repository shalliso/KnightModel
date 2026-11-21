import KnightModel.RankTwo.Atlas
import Mathlib.Order.Hom.Set

/-! # Change of coordinates and limit-sector transport

The value of a change of coordinates is defined on every word. All changes
compose on the nose. At a limit sector a convex-range word embedding agreeing
on cofinally many marks already restricts to the required isomorphism.
-/

namespace KnightModel.RankTwo.MarkedRows

variable {J W : Type*} [LinearOrder J] [LinearOrder W] [OrderTop W]
variable (D : MarkedRows J W)

theorem sector_eq_Iic_of_first {a b : J} (h : ∀ i : J, ¬ i < a) :
    D.sector b a = Set.Iic (D.mark b a) := by
  ext w
  exact ⟨And.left, fun hw => ⟨hw, fun i hi => (h i hi).elim⟩⟩

theorem sector_eq_Ioc_of_predecessor {p a b : J} (hpa : p < a) (hab : a ≤ b)
    (hprev : ∀ i < a, i ≤ p) : D.sector b a = Set.Ioc (D.mark b p) (D.mark b a) := by
  ext w
  constructor
  · intro hw
    exact ⟨hw.2 p hpa, hw.1⟩
  · rintro ⟨hp, ha⟩
    refine ⟨ha, fun i hi => ?_⟩
    exact (D.mark_strictMonoOn b |>.monotoneOn (hi.le.trans hab)
      (hpa.le.trans hab) (hprev i hi)).trans_lt hp

/-- A local embedding prescribing the new upper mark and agreeing on a cofinal
set of earlier marks carries the entire sector across, including its lower cut. -/
noncomputable def sectorIsoOfCofinal {a b : J} (hab : a ≤ b)
    (nonfirst : ∃ i : J, i < a) (f : W ↪o W)
    (convex : ∀ {u v w : W}, f u ≤ w → w ≤ f v → w ∈ Set.range f)
    (endpoint : f (D.mark a a) = D.mark b a)
    (agree : ∀ i < a, ∃ j, i ≤ j ∧ j < a ∧ f (D.mark a j) = D.mark b j) :
    D.sector a a ≃o D.sector b a := by
  let g : D.sector a a → D.sector b a := fun x => ⟨f x, by
    refine ⟨endpoint ▸ f.monotone x.property.1, ?_⟩
    intro i hi
    obtain ⟨j, hij, hja, hj⟩ := agree i hi
    have hle := (D.mark_strictMonoOn b).monotoneOn (hi.le.trans hab) (hja.le.trans hab) hij
    exact hle.trans_lt (hj ▸ f.strictMono (x.property.2 j hja))⟩
  have hm : StrictMono g := fun _ _ h => f.strictMono h
  have hs : Function.Surjective g := by
    intro y
    obtain ⟨i, hi⟩ := nonfirst
    obtain ⟨j, _, hja, hj⟩ := agree i hi
    have lo : f (D.mark a j) ≤ y := hj ▸ (y.property.2 j hja).le
    have up : (y : W) ≤ f (D.mark a a) := endpoint ▸ y.property.1
    obtain ⟨w, hw⟩ := convex lo up
    have hmem : w ∈ D.sector a a := by
      refine ⟨f.le_iff_le.mp (hw ▸ up), ?_⟩
      intro k hk
      obtain ⟨l, hkl, hla, hl⟩ := agree k hk
      have hle := (D.mark_strictMonoOn a).monotoneOn hk.le hla.le hkl
      exact hle.trans_lt (f.lt_iff_lt.mp (by rw [hl, hw]; exact y.property.2 l hla))
    exact ⟨⟨w, hmem⟩, Subtype.ext hw⟩
  exact StrictMono.orderIsoOfRightInverse _ hm (fun y => (hs y).choose)
    (fun y => (hs y).choose_spec)

variable [WellFoundedLT J] (q : D.Transports)

def includeInitial {a b : J} (hab : a ≤ b) (x : Set.Iic (D.anchor a)) :
    Set.Iic (D.anchor b) :=
  ⟨x.val, x.property.trans (D.anchor_strictMono.monotone hab)⟩

/-- Read the point with coordinate `w` in an earlier chart in the later chart. -/
noncomputable def change {a b : J} (hab : a ≤ b) : W ↪o W :=
  OrderEmbedding.ofStrictMono
    (fun w => D.chart q b (D.includeInitial hab ((D.chart q a).symm w)))
    (fun _ _ h => (D.chart q b).strictMono ((D.chart q a).symm.strictMono h))

@[simp] theorem change_chart {a b : J} (hab : a ≤ b) (x : Set.Iic (D.anchor a)) :
    D.change q hab (D.chart q a x) = D.chart q b (D.includeInitial hab x) := by
  change D.chart q b (D.includeInitial hab ((D.chart q a).symm (D.chart q a x))) = _
  rw [OrderIso.symm_apply_apply]

theorem change_comp {a b c : J} (hab : a ≤ b) (hbc : b ≤ c) (w : W) :
    D.change q hbc (D.change q hab w) = D.change q (hab.trans hbc) w := by
  obtain ⟨x, rfl⟩ := (D.chart q a).surjective w
  simp only [change_chart]
  rfl

@[simp] theorem change_self (a : J) (w : W) : D.change q (le_refl a) w = w := by
  obtain ⟨x, rfl⟩ := (D.chart q a).surjective w
  rw [change_chart]
  rfl

theorem range_change {a b : J} (hab : a ≤ b) :
    Set.range (D.change q hab) = Set.Iic (D.mark b a) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨x, rfl⟩ := (D.chart q a).surjective v
    rw [change_chart]
    change D.chart q b (D.includeInitial hab x) ≤ D.mark b a
    rw [← D.chart_anchor q hab]
    exact (D.chart q b).monotone x.property
  · intro hw
    let y := (D.chart q b).symm w
    have hy : y.val ≤ D.anchor a := by
      change y ≤ (⟨D.anchor a, D.le_anchor_iff.mpr hab⟩ : Set.Iic (D.anchor b))
      apply (D.chart q b).le_iff_le.mp
      simpa only [y, OrderIso.apply_symm_apply, D.chart_anchor q hab] using hw
    let x : Set.Iic (D.anchor a) := ⟨y.val, hy⟩
    refine ⟨D.chart q a x, ?_⟩
    rw [change_chart]
    exact (D.chart q b).apply_symm_apply w

end KnightModel.RankTwo.MarkedRows
