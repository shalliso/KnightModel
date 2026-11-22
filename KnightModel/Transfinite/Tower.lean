import KnightModel.Transfinite.Zero
import KnightModel.Transfinite.Atlas
import KnightModel.Transfinite.ComparisonSuccessor
import KnightModel.Transfinite.Limit
import KnightModel.Transfinite.SuccessorScott

/-! # The countable ordinal tower

The countable seed and all its rank bounds are constructed before square
sequences are chosen. Square below a stage is used only for its large model.
At a limit, the named countable sum can enumerate every earlier stage.
-/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott Cardinal

noncomputable section

/-- The coherent ladder hypotheses below one target ordinal. -/
def SquaresBelow (α : Ordinal.{0}) : Prop :=
  ∀ β < α, Nonempty (SquareLadders (AtlasIndex (aleph β)) (aleph β).ord)

theorem SquaresBelow.restrict {α β : Ordinal.{0}} (h : β ≤ α) (sq : SquaresBelow α) :
    SquaresBelow β := fun γ hγ => sq γ (hγ.trans_le h)

abbrev Seed.TupleLE (P : Seed) (α : Ordinal.{0}) : Prop :=
  ∀ {n : ℕ} (x : Fin n → P.M), ComparisonLE α (⊤ : Subgroup ↥(automorphismGroup P.D)) x

abbrev Seed.TupleLT (P : Seed) (α : Ordinal.{0}) : Prop :=
  ∀ {n : ℕ} (x : Fin n → P.M), ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup P.D)) x

theorem Seed.singletonLT (P : Seed) {α : Ordinal.{0}} (ht : P.TupleLT α) (x : P.M) :
    ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup P.D)) x := by
  obtain ⟨β, hb, hr⟩ := ht (fun _ : Fin 1 => x)
  refine ⟨β, hb, hr.of_stabilizer fun g _ => ?_⟩
  rw [tuple_fixed_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- The induction data record the stronger bounds at limits and after
infinite predecessors. The realization is conditional on square; the seed
and all the comparison bounds are independent of square. -/
structure Stage (α : Ordinal.{0}) where
  seed : Seed
  rank : seed.TupleLE α
  limit_rank : Order.IsSuccLimit α → seed.TupleLT α
  infinite_succ_rank : ∀ β, α = Order.succ β → Ordinal.omega0 ≤ β → seed.TupleLE β
  realizes : SquaresBelow α → Nonempty (seed.Realizes (aleph α))

private structure StageBuilders where
  succ : Seed → Seed
  succ_rank (P : Seed) {α : Ordinal.{0}} (h : α ≠ 0) : P.TupleLT α → (succ P).TupleLE α
  succ_real (P : Seed) (κ : Cardinal.{0}) : P.Realizes κ → ℵ₀ ≤ κ →
    SquareLadders (AtlasIndex κ) κ.ord → (succ P).Realizes (Order.succ κ)
  sum : (ℕ → Seed) → Seed
  sum_rank (P : ℕ → Seed) {α : Ordinal.{0}} (h : Order.IsSuccLimit α) :
    (∀ i (x : (P i).M), ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup (P i).D)) x) →
      (sum P).TupleLT α
  sum_real (P : ℕ → Seed) (k : ℕ → Cardinal.{0}) (κ : Cardinal.{0}) : ℵ₀ ≤ κ →
    (∀ i, k i ≤ κ) → (∀ c, (∀ i, k i ≤ c) → κ ≤ c) →
      (∀ i, (P i).Realizes (k i)) → (sum P).Realizes κ

private def stageZero : Stage 0 where
  seed := zeroSeed
  rank := zeroSeed_tuple
  limit_rank h := (Ordinal.not_isSuccLimit_zero h).elim
  infinite_succ_rank β eq _ := (Order.succ_ne_bot β eq.symm).elim
  realizes _ := ⟨by simpa using zeroSeed_realizes⟩

/-- Every infinite stage already has a strict tuple bound at its own index. -/
theorem Stage.strict_infinite {α : Ordinal.{0}} (S : Stage α) (h : Ordinal.omega0 ≤ α) :
    S.seed.TupleLT α := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨β, rfl⟩ | hl
  · exact (not_lt_of_ge h Ordinal.omega0_pos).elim
  · have hb : Ordinal.omega0 ≤ β := Ordinal.isSuccLimit_omega0.le_succ_iff.mp h
    intro n x
    exact ⟨β, Order.lt_succ β, S.infinite_succ_rank β rfl hb x⟩
  · exact S.limit_rank hl

private def stageSucc (B : StageBuilders) {α : Ordinal.{0}} (S : Stage α) :
    Stage (Order.succ α) where
  seed := B.succ S.seed
  rank := B.succ_rank S.seed (Order.succ_ne_bot _) (fun x => ⟨_, Order.lt_succ α, S.rank x⟩)
  limit_rank h := (Order.not_isSuccLimit_succ _ h).elim
  infinite_succ_rank β eq h := by
    obtain rfl := Order.succ_injective eq
    exact B.succ_rank S.seed (ne_of_gt (Ordinal.omega0_pos.trans_le h)) (S.strict_infinite h)
  realizes sq := by
    obtain ⟨Q⟩ := S.realizes (sq.restrict (Order.le_succ _))
    obtain ⟨L⟩ := sq α (Order.lt_succ _)
    rw [Order.succ_eq_add_one, ← Cardinal.succ_aleph]
    exact ⟨B.succ_real S.seed _ Q (Cardinal.aleph0_le_aleph _) L⟩

private def stageLimit (B : StageBuilders) {α : Ordinal.{0}} (hlim : Order.IsSuccLimit α)
    (count : α.card ≤ ℵ₀) (prev : ∀ β < α, Nonempty (Stage β)) : Stage α := by
  letI : Countable α.ToType := Cardinal.mk_le_aleph0_iff.mp (by simpa using count)
  letI : Countable (Set.Iio α) := Ordinal.ToType.mk.injective.countable
  letI : Nonempty (Set.Iio α) := ⟨⟨0, hlim.pos⟩⟩
  let e := Classical.choose (exists_surjective_nat (Set.Iio α))
  have onto : Function.Surjective e := Classical.choose_spec (exists_surjective_nat (Set.Iio α))
  let S (i : ℕ) : Stage (e i).1 := Classical.choice (prev _ (e i).2)
  let P (i : ℕ) := (S i).seed
  have low : (B.sum P).TupleLT α := by
    apply B.sum_rank P hlim
    intro i x
    exact (P i).singletonLT (fun t => ⟨_, (e i).2, (S i).rank t⟩) x
  refine ⟨B.sum P, ?_, fun _ => low, ?_, ?_⟩
  · intro n x
    obtain ⟨β, hb, hr⟩ := low x
    exact hr.mono hb.le
  · intro β eq _
    exact (hlim.succ_ne β eq.symm).elim
  · intro sq
    refine ⟨B.sum_real P (fun i => aleph (e i).1) (aleph α) (aleph0_le_aleph _) ?_ ?_ ?_⟩
    · exact fun i => Cardinal.aleph_le_aleph.mpr (e i).2.le
    · intro c h
      rw [Cardinal.aleph_limit hlim]
      apply ciSup_le
      intro β
      obtain ⟨i, rfl⟩ := onto β
      exact h i
    · exact fun i => Classical.choice ((S i).realizes (sq.restrict (e i).2.le))

private theorem stages_of_builders (B : StageBuilders) (α : Ordinal.{0}) (hc : α.card ≤ ℵ₀) :
    Nonempty (Stage α) := by
  induction α using Ordinal.limitRecOn with
  | zero => exact ⟨stageZero⟩
  | add_one α ih =>
    exact ⟨stageSucc B (Classical.choice (ih ((Ordinal.card_le_card (Order.le_succ _)).trans hc)))⟩
  | limit α hlim ih =>
    exact ⟨stageLimit B hlim hc fun β hβ => ih β hβ ((Ordinal.card_le_card hβ.le).trans hc)⟩


private def concreteBuilders : StageBuilders where
  succ := successorSeed
  succ_rank P h lo _ x := successorSeed_tuple_comparisonLE P h (fun _ t => lo t) _ x
  succ_real P _ Q h S := successorRealizes P Q h S
  sum := sumSeed
  sum_rank P h lo _ x := sumSeed_tuple_lt P h lo x
  sum_real := sumSeed_realizes

/-- For every countable ordinal the actual recursion produces a single
countable seed, with all the rank and conditional realization claims in
`Stage`. No successor or limit construction is a hypothesis of this result. -/
theorem stages (α : Ordinal.{0}) (hc : α.card ≤ ℵ₀) : Nonempty (Stage α) :=
  stages_of_builders concreteBuilders α hc

end
end KnightModel.Transfinite
