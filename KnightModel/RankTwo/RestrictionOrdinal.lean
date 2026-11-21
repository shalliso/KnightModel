import KnightModel.RankTwo.Restriction
import Mathlib.SetTheory.Cardinal.Regular

/-! # The stabilization index ω₁

The abstract hypotheses on the stages of `countable_joint_profiles` hold on
the first uncountable ordinal. -/

namespace KnightModel.RankTwo.Restriction

open Cardinal Set

abbrev OmegaOne := (aleph.{0} 1).ord.ToType

private theorem countable_bounded {s : Set OmegaOne} (hs : s.Countable) : BddAbove s := by
  apply BddAbove.of_not_isCofinal
  intro hc
  have h := Order.cof_le hc
  rw [Ordinal.cof_toType, isRegular_aleph_one.cof_ord] at h
  exact aleph0_lt_aleph_one.not_ge (h.trans (le_aleph0_iff_set_countable.mpr hs))

/-- The standard realization of countably directed stages. -/
noncomputable def omegaOneStages : Stages OmegaOne where
  start := Classical.choice (show Nonempty OmegaOne by
    rw [Ordinal.nonempty_toType_iff]
    simpa only [ord_aleph] using (Ordinal.omega_pos 1).ne')
  le := (· ≤ ·)
  refl := le_refl
  trans := le_trans
  bounded := by
    intro f
    obtain ⟨i, hi⟩ := countable_bounded (countable_range f)
    exact ⟨i, fun n => hi (mem_range_self n)⟩

/-- The stages before a given countable ordinal have a countable cover. -/
theorem omegaOne_initial (i : OmegaOne) :
    CountablyCovered (fun j => ¬ omegaOneStages.le i j) := by
  haveI : Nonempty OmegaOne := ⟨i⟩
  have h : (Iio i).Countable := le_aleph0_iff_set_countable.mp <|
    lt_aleph_one_iff.mp (by simpa using mk_Iio_lt i (by simp))
  obtain ⟨f, hf⟩ := countable_iff_exists_subset_range.mp h
  exact ⟨f, fun j hj => hf (lt_of_not_ge hj)⟩

/-- A countable set of parameters supports only countably many profiles on
an ω₁-comparison chain satisfying the finite Scott orbit extension rules. -/
theorem omegaOne_countable_joint_profiles (T : TuplePartitions omegaOneStages X)
    (good : X → Prop) (low : ∀ a, good a → ∀ u, (∀ x ∈ u, good x) → T.lowOver u a)
    (parameters : ℕ → List X) (hparam : ∀ n x, x ∈ parameters n → good x)
    (label : OmegaOne → OmegaOne → ℕ) (joint : OmegaOne → List X → ℕ)
    (readout : ∀ k u v, (T.atStage k).r u v → joint k u = joint k v)
    (transport : ∀ i j k, i ≤ j → i ≤ k → label i j = label i k →
      ∀ u, ∃ v, (T.atStage i).r v u ∧ joint j u = joint k v) :
    (range (fun j n => joint j (parameters n))).Countable := by
  obtain ⟨f, hf⟩ := countable_joint_profiles omegaOneStages T omegaOne_initial good low
    parameters hparam label joint readout transport
  exact countable_iff_exists_subset_range.mpr ⟨f, fun _ hy => hf _ hy⟩

end KnightModel.RankTwo.Restriction
