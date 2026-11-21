import KnightModel.RankTwo.RestrictionOrdinal
import KnightModel.RankTwo.RestrictionFiltration
import KnightModel.RankTwo.Cardinality
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-! # The restriction trees

The local orders in a chart only compare points of its own color. All their
principal lower sets are countable. A cofinal branch through the tree of
restrictions would extend those conditions to all of ω₂.
-/

namespace KnightModel.RankTwo.Restriction

open Cardinal Set

abbrev OmegaTwo := (aleph.{0} 2).ord.ToType

/-- At level α, use all rows whose endpoint is at least α. The values of a
row outside its intended initial segment never enter the restriction tree. -/
def chartLevel (rows : OmegaTwo → Chart OmegaTwo) (a : OmegaTwo) : Set (Chart (Iio a)) :=
  {t | ∃ b, a ≤ b ∧ t = (rows b).comap Subtype.val}

/-- As in a tree of functions ordered by restriction, a cofinal branch is a
full function all of whose initial restrictions appear in the tree. -/
def FullChart (rows : OmegaTwo → Chart OmegaTwo) (C : Chart OmegaTwo) :=
  ∀ a, C.comap (Subtype.val : Iio a → _) ∈ chartLevel rows a

private theorem one_lt_two : ℵ₁ < aleph.{0} 2 := aleph_lt_aleph.mpr (by decide)

private theorem bounded_below_two {s : Set OmegaTwo} (hs : #s ≤ ℵ₁) :
    ∃ a : OmegaTwo, ∀ x ∈ s, x < a := by
  apply Order.not_isCofinal_iff.mp
  intro h
  have hc := Order.cof_le h
  have hr : IsRegular (aleph.{0} 2) := isRegular_aleph_add_one 1
  rw [Ordinal.cof_toType, hr.cof_ord] at hc
  exact one_lt_two.not_ge (hc.trans hs)

private theorem has_later (i : OmegaTwo) : ∃ j, i < j := by
  obtain ⟨j, hj⟩ := bounded_below_two (s := {i}) (by simp)
  exact ⟨j, hj i (mem_singleton i)⟩

private theorem chart_agreement {rows : OmegaTwo → Chart OmegaTwo} {C : Chart OmegaTwo}
    (branch : FullChart rows C) (a : OmegaTwo) :
    ∃ b ≥ a, (∀ x < a, C.color x = (rows b).color x) ∧
      (∀ x < a, ∀ y < a, C.rel x y ↔ (rows b).rel x y) := by
  obtain ⟨b, hab, he⟩ := branch a
  refine ⟨b, hab, fun x hx => ?_, fun x hx y hy => ?_⟩
  · exact congrArg (fun t : Chart (Iio a) => t.color ⟨x, hx⟩) he
  · exact iff_of_eq (congrArg (fun t : Chart (Iio a) => t.rel ⟨x, hx⟩ ⟨y, hy⟩) he)

/-- Models the two types of relative rank-one fibers uniformly: on a countable
witness-clause fiber one can use the ordinal order as its comparison. -/
structure LocalCharts (rows : OmegaTwo → Chart OmegaTwo) : Prop where
  compare : ∀ b x y, x < b → y < b → (rows b).color x = (rows b).color y →
    (rows b).rel x y ∨ (rows b).rel y x
  small : ∀ b x, x < b →
    {y | y < b ∧ (rows b).color y = (rows b).color x ∧ (rows b).rel y x}.Countable

/-- No cofinal branch exists. The proof reflects any putative uncountable
lower cone to one bounded row by regularity of ω₂. -/
theorem no_full_chart {rows : OmegaTwo → Chart OmegaTwo} (H : LocalCharts rows)
    (C : Chart OmegaTwo) : ¬ FullChart rows C := by
  intro branch
  have cmp (x y : OmegaTwo) (h : C.color x = C.color y) : C.rel x y ∨ C.rel y x := by
    obtain ⟨a, ha⟩ := has_later (max x y)
    have hx := lt_of_le_of_lt (le_max_left x y) ha
    have hy := lt_of_le_of_lt (le_max_right x y) ha
    obtain ⟨b, hab, col, rel⟩ := chart_agreement branch a
    exact (H.compare b x y (hx.trans_le hab) (hy.trans_le hab)
      ((col x hx).symm.trans (h.trans (col y hy)))).imp
      (rel x hx y hy).mpr (rel y hy x hx).mpr
  have small (x : OmegaTwo) : {y | C.color y = C.color x ∧ C.rel y x}.Countable := by
    by_contra h
    have hcard := lt_of_not_ge (fun hc => h (le_aleph0_iff_set_countable.mp hc))
    obtain ⟨s, hsub, hs⟩ := le_mk_iff_exists_subset.mp (aleph_one_le_iff.mpr hcard)
    obtain ⟨a₁, ha₁⟩ := bounded_below_two hs.le
    obtain ⟨a₂, ha₂⟩ := has_later x
    let a := max a₁ a₂
    have hx : x < a := lt_of_lt_of_le ha₂ (le_max_right _ _)
    obtain ⟨b, hab, col, rel⟩ := chart_agreement branch a
    have hc := (H.small b x (hx.trans_le hab)).mono (s₁ := s) (by
      intro y hy
      have hy' : y < a := lt_of_lt_of_le (ha₁ y hy) (le_max_left _ _)
      have hxy := hsub hy
      exact ⟨hy'.trans_le hab, (col y hy').symm.trans (hxy.1.trans (col x hx)),
        (rel y hy' x hx).mp hxy.2⟩)
    exact aleph0_lt_aleph_one.not_ge (hs ▸ le_aleph0_iff_set_countable.mpr hc)
  obtain ⟨n, hn⟩ := infinite_pigeonhole C.color
    (by simpa only [mk_toType, card_ord] using aleph0_le_aleph 2)
    (by simpa only [mk_nat, mk_toType, card_ord, (isRegular_aleph_add_one 1).cof_ord]
          using aleph0_lt_aleph_one.trans one_lt_two)
  let F := C.color ⁻¹' {n}
  have bound : #F ≤ ℵ₁ := by
    let lower (v : F) : Set F := {w | C.rel w.val v.val}
    have hs (v : F) : #(lower v) ≤ ℵ₀ := by
      apply mk_le_aleph0_iff.mpr
      let intoCone (w : lower v) : {y // C.color y = C.color v.val ∧ C.rel y v.val} :=
        ⟨w.val.val, w.val.property.trans v.property.symm, w.property⟩
      haveI : Countable {y // C.color y = C.color v.val ∧ C.rel y v.val} := small v.val
      exact Function.Injective.countable (f := intoCone) (fun u w e =>
        Subtype.ext (Subtype.ext (congrArg Subtype.val e)))
    simpa only [succ_aleph0] using
      cardinal_le_succ_of_pair_cover (X := F) (κ := ℵ₀) le_rfl lower hs
        (fun x y => cmp x.val y.val (x.property.trans y.property.symm))
  have hf : #F = aleph 2 := by simpa only [mk_toType, card_ord] using hn
  exact one_lt_two.not_ge (hf ▸ bound)

/-- Countability of the chart traces on countable parts of any level. -/
def SmallTraces (rows : OmegaTwo → Chart OmegaTwo) :=
  ∀ a (s : Set (Iio a)), s.Countable →
    (range (fun t : chartLevel rows a => t.val.comap (Subtype.val : s → _))).Countable

private def oneFiltration {X : Type} (f : X ↪ OmegaOne) : Filtration omegaOneStages X where
  mem i x := f x ≤ i
  mono h h' := le_trans h' h
  exhaustive x := ⟨f x, le_rfl⟩

private theorem countable_oneFiltration {X : Type} (f : X ↪ OmegaOne) (i : OmegaOne) :
    {x | (oneFiltration f).mem i x}.Countable := by
  haveI : Nonempty OmegaOne := ⟨i⟩
  obtain ⟨g, hg⟩ := omegaOne_initial i
  have hs : (Iio i).Countable := countable_iff_exists_subset_range.mpr
    ⟨g, fun x hx => hg _ (not_le.mpr hx)⟩
  have ht : (Iic i).Countable := Set.Iio_insert (a := i) ▸ hs.insert i
  exact ht.preimage f.injective

/-- A level wider than ℵ₁ yields an ordinary ω₁-Kurepa tree: its levels
are countable, even though the original level may support ℵ₂ different rows. -/
noncomputable def kurepaOfWideLevel {rows : OmegaTwo → Chart OmegaTwo}
    (small : SmallTraces rows) (a : OmegaTwo) (wide : ℵ₁ < #(chartLevel rows a)) :
    CountableLevelTree omegaOneStages OmegaTwo := by
  haveI : Nonempty OmegaTwo := ⟨a⟩
  have hdom : #(Iio a) ≤ ℵ₁ := by
    apply Order.lt_succ_iff.mp
    simpa only [succ_aleph, one_add_one_eq_two, mk_toType, card_ord] using
      mk_Iio_lt a (by simp)
  let f := Classical.choice ((le_def (Iio a) OmegaOne).mp
    (by simpa only [mk_toType, card_ord] using hdom))
  have hsize : #OmegaTwo ≤ #(chartLevel rows a) := by
    simpa only [mk_toType, card_ord, succ_aleph, one_add_one_eq_two] using
      (Order.succ_le_iff.mpr wide)
  let e := Classical.choice ((le_def OmegaTwo (chartLevel rows a)).mp hsize)
  let chart (b : OmegaTwo) := (e b).val
  let F := oneFiltration f
  apply F.treeOfTraces chart (fun b c h => e.injective (Subtype.ext h))
  intro i
  let s : Set (Iio a) := {x | F.mem i x}
  have htrace := small a s (countable_oneFiltration f i)
  let p₀ : Chart (F.Piece i) := F.trace (chart a) i
  haveI : Nonempty (Chart (F.Piece i)) := ⟨p₀⟩
  obtain ⟨g, hg⟩ := countable_iff_exists_subset_range.mp htrace
  exact ⟨g, fun _ ⟨b, hb⟩ => hg ⟨e b, hb.symm⟩⟩

/-- The restriction-tree alternative. The first disjunct gives the branchless
ω₂-tree in its concrete representation by rows and their restrictions. -/
theorem restriction_tree_alternative {rows : OmegaTwo → Chart OmegaTwo}
    (localCharts : LocalCharts rows) (small : SmallTraces rows) :
    ((∀ a, #(chartLevel rows a) ≤ ℵ₁) ∧ ¬ ∃ C, FullChart rows C) ∨
      Nonempty (CountableLevelTree.{0, 0, 0} omegaOneStages OmegaTwo) := by
  by_cases narrow : ∀ a, #(chartLevel rows a) ≤ ℵ₁
  · exact Or.inl ⟨narrow, fun ⟨C, hC⟩ => no_full_chart localCharts C hC⟩
  · obtain ⟨a, ha⟩ := not_forall.mp narrow
    exact Or.inr ⟨kurepaOfWideLevel small a (lt_of_not_ge ha)⟩

end KnightModel.RankTwo.Restriction
