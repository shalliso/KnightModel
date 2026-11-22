import KnightModel.Transfinite.ComparisonSuccessor
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.SetTheory.Ordinal.Principal

/-! # Finite tuples strictly below a limit rank

For two ordinal bounds, double the larger bound on the left and add one for a
tie. Lowering a largest coordinate strictly decreases this ordinal. Every
nonzero limit is divisible by ω, so neither doubling on the left nor this
finite tie correction can cross a limit. Iterating over finite tuples gives
the limit closure needed for disjoint unions.
-/

namespace KnightModel.Transfinite

universe w

/-- The left factor is finite, even for transfinite coordinate ranks. -/
noncomputable def pairMeasure (a b : Ordinal.{w}) : Ordinal.{w} :=
  2 * max a b + if a = b then 1 else 0

theorem pairMeasure_comm (a b : Ordinal.{w}) : pairMeasure a b = pairMeasure b a := by
  simp only [pairMeasure, max_comm a b, eq_comm]

private theorem pairMeasure_lt_next (a b : Ordinal.{w}) :
    pairMeasure a b < 2 * (max a b + 1) := by
  unfold pairMeasure
  rw [mul_add_one]
  apply add_lt_add_right
  split
  · exact one_lt_two
  · exact zero_lt_two

theorem pairMeasure_drop_left {a b c : Ordinal.{w}} (hba : b ≤ a) (hca : c < a) :
    pairMeasure c b < pairMeasure a b := by
  rcases hba.eq_or_lt with rfl | hba
  · simp [pairMeasure, max_eq_right hca.le, hca.ne]
  · have h : max c b < a := max_lt hca hba
    calc
      pairMeasure c b < 2 * (max c b + 1) := pairMeasure_lt_next ..
      _ ≤ 2 * a := by
        apply mul_le_mul_right
        simpa only [← Order.succ_eq_add_one] using (Order.succ_le_iff.mpr h)
      _ = pairMeasure a b := by simp [pairMeasure, max_eq_left hba.le, hba.ne']

theorem pairMeasure_drop_right {a b c : Ordinal.{w}} (hab : a ≤ b) (hcb : c < b) :
    pairMeasure a c < pairMeasure a b := by
  simpa only [pairMeasure_comm a c, pairMeasure_comm a b] using pairMeasure_drop_left hab hcb

theorem pairMeasure_lt_limit {a b lim : Ordinal.{w}} (hlim : Order.IsSuccLimit lim)
    (ha : a < lim) (hb : b < lim) : pairMeasure a b < lim := by
  have hnext : max a b + 1 < lim := hlim.succ_lt (max_lt ha hb)
  have twoω : (2 : Ordinal.{w}) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 2
  have hmul : 2 * lim = lim :=
    Ordinal.mul_omega0_dvd zero_lt_two twoω
      (Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlim.isSuccPrelimit)
  exact (pairMeasure_lt_next ..).trans
    (hmul ▸ (mul_lt_mul_iff_right₀ (zero_lt_two : (0 : Ordinal) < 2)).2 hnext)

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

private theorem prod_left_sub (H : Subgroup G) (x : X) (y : Y) :
    H ⊓ MulAction.stabilizer G (x,y) ≤ H ⊓ MulAction.stabilizer G x :=
  fun _ hg => ⟨hg.1, congrArg Prod.fst (show _ • (x,y) = (x,y) from hg.2)⟩

private theorem prod_right_sub (H : Subgroup G) (x : X) (y : Y) :
    H ⊓ MulAction.stabilizer G (x,y) ≤ H ⊓ MulAction.stabilizer G y :=
  fun _ hg => ⟨hg.1, congrArg Prod.snd (show _ • (x,y) = (x,y) from hg.2)⟩

/-- An explicit comparison bound for a pair, without assumptions of
independence or commutation of the two actions. -/
theorem comparisonLE_prod {a b : Ordinal.{w}} {H : Subgroup G} {x : X} {y : Y}
    (hx : ComparisonLE a H x) (hy : ComparisonLE b H y) :
    ComparisonLE (pairMeasure a b) H (x,y) := by
  by_cases hz : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hz
    apply ComparisonLE.mono (zero_le : (0 : Ordinal.{w}) ≤ _)
    apply (comparisonLE_zero ..).2
    exact fun g hg => Prod.ext ((comparisonLE_zero ..).1 hx g hg) ((comparisonLE_zero ..).1 hy g hg)
  have hm : pairMeasure a b ≠ 0 := by
    have hp : 0 < max a b := lt_of_le_of_ne zero_le fun he =>
      hz ⟨le_antisymm (he ▸ le_max_left a b) zero_le, le_antisymm (he ▸ le_max_right a b) zero_le⟩
    exact ne_of_gt (lt_of_lt_of_le (mul_pos (zero_lt_two : (0 : Ordinal) < 2) hp) le_self_add)
  apply (comparisonLE_iff_of_ne_zero hm ..).2
  intro g hg
  rcases le_total b a with hba | hab
  · have ha : a ≠ 0 := fun h => hz ⟨h, le_antisymm (h ▸ hba) zero_le⟩
    rcases (comparisonLE_iff_of_ne_zero ha ..).1 hx g hg with ⟨c, hc, h⟩ | ⟨c, hc, h⟩
    · exact Or.inl ⟨_, pairMeasure_drop_left hba hc,
        comparisonLE_prod (h.restrict (prod_left_sub H (g • x) (g • y))) (hy.restrict inf_le_left)⟩
    · exact Or.inr ⟨_, pairMeasure_drop_left hba hc,
        comparisonLE_prod (h.restrict (prod_left_sub H x y))
          ((hy.translate g hg).restrict inf_le_left)⟩
  · have hb : b ≠ 0 := fun h => hz ⟨le_antisymm (h ▸ hab) zero_le, h⟩
    rcases (comparisonLE_iff_of_ne_zero hb ..).1 hy g hg with ⟨c, hc, h⟩ | ⟨c, hc, h⟩
    · exact Or.inl ⟨_, pairMeasure_drop_right hab hc,
        comparisonLE_prod (hx.restrict inf_le_left) (h.restrict (prod_right_sub H (g • x) (g • y)))⟩
    · exact Or.inr ⟨_, pairMeasure_drop_right hab hc,
        comparisonLE_prod ((hx.translate g hg).restrict inf_le_left)
          (h.restrict (prod_right_sub H x y))⟩
termination_by pairMeasure a b
decreasing_by
  all_goals first | apply pairMeasure_drop_left <;> assumption
                  | apply pairMeasure_drop_right <;> assumption

theorem comparisonLT_prod {lim : Ordinal.{w}} (hlim : Order.IsSuccLimit lim)
    {H : Subgroup G} {x : X} {y : Y} (hx : ComparisonLT lim H x) (hy : ComparisonLT lim H y) :
    ComparisonLT lim H (x,y) := by
  obtain ⟨a, ha, hx⟩ := hx
  obtain ⟨b, hb, hy⟩ := hy
  exact ⟨_, pairMeasure_lt_limit hlim ha hb, comparisonLE_prod hx hy⟩

/-- Component ranks below a nonzero limit give a strict bound for every
finite tuple, even when the component bounds are unbounded in that limit. -/
theorem comparisonLT_tuple {lim : Ordinal.{w}} (hlim : Order.IsSuccLimit lim)
    {H : Subgroup G} {n : ℕ} (x : Fin n → X) (hr : ∀ i, ComparisonLT lim H (x i)) :
    ComparisonLT lim H x := by
  induction n with
  | zero =>
    exact ⟨0, hlim.pos, (comparisonLE_zero ..).2 fun _ _ => Subsingleton.elim ..⟩
  | succ n ih =>
    obtain ⟨a, ha, hp⟩ := comparisonLT_prod hlim (hr 0) (ih (Fin.tail x) (fun i => hr i.succ))
    refine ⟨a, ha, hp.of_stabilizer fun g _ => ?_⟩
    rw [tuple_fixed_iff, Fin.forall_fin_succ, Prod.ext_iff]
    exact and_congr Iff.rfl (tuple_fixed_iff g (Fin.tail x))

end KnightModel.Transfinite
