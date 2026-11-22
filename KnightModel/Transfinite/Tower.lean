import KnightModel.Transfinite.Zero
import KnightModel.Transfinite.SquareOmega
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

/-- Only uncountable predecessor cardinals require square assumptions. -/
theorem squaresBelow_iff_positive (α : Ordinal.{0}) : SquaresBelow α ↔
    ∀ β, 0 < β → β < α → Nonempty (SquareLadders (AtlasIndex (aleph β)) (aleph β).ord) := by
  refine ⟨fun sq β _ h => sq β h, ?_⟩
  intro h β hβ
  rcases eq_or_lt_of_le (zero_le : 0 ≤ β) with rfl | pos
  · let L (κ : Cardinal.{0}) := Nonempty (SquareLadders (AtlasIndex κ) κ.ord)
    exact (congrArg L Cardinal.aleph_zero).mpr squareLadders_aleph0
  · exact h β pos hβ

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

private def stageSucc {α : Ordinal.{0}} (S : Stage α) :
    Stage (Order.succ α) where
  seed := successorSeed S.seed
  rank := fun {n} t => successorSeed_tuple_comparisonLE S.seed (Order.succ_ne_bot _)
    (fun _ x => ⟨_, Order.lt_succ α, S.rank x⟩) n t
  limit_rank h := (Order.not_isSuccLimit_succ _ h).elim
  infinite_succ_rank β eq h := by
    obtain rfl := Order.succ_injective eq
    intro n t
    exact successorSeed_tuple_comparisonLE S.seed (ne_of_gt (Ordinal.omega0_pos.trans_le h))
      (fun _ x => S.strict_infinite h x) n t
  realizes sq := by
    obtain ⟨Q⟩ := S.realizes (sq.restrict (Order.le_succ _))
    obtain ⟨L⟩ := sq α (Order.lt_succ _)
    rw [Order.succ_eq_add_one, ← Cardinal.succ_aleph]
    exact ⟨successorRealizes S.seed Q (Cardinal.aleph0_le_aleph _) L⟩

private def stageLimit {α : Ordinal.{0}} (hlim : Order.IsSuccLimit α)
    (count : α.card ≤ ℵ₀) (prev : ∀ β < α, Nonempty (Stage β)) : Stage α := by
  letI : Countable α.ToType := Cardinal.mk_le_aleph0_iff.mp (by simpa using count)
  letI : Countable (Set.Iio α) := Ordinal.ToType.mk.injective.countable
  letI : Nonempty (Set.Iio α) := ⟨⟨0, hlim.pos⟩⟩
  let e := Classical.choose (exists_surjective_nat (Set.Iio α))
  have onto : Function.Surjective e := Classical.choose_spec (exists_surjective_nat (Set.Iio α))
  let S (i : ℕ) : Stage (e i).1 := Classical.choice (prev _ (e i).2)
  let P (i : ℕ) := (S i).seed
  have low : (sumSeed P).TupleLT α := by
    intro _ t
    apply sumSeed_tuple_lt P hlim _ t
    intro i x
    exact (P i).singletonLT (fun t => ⟨_, (e i).2, (S i).rank t⟩) x
  refine ⟨sumSeed P, ?_, fun _ => low, ?_, ?_⟩
  · intro n x
    obtain ⟨β, hb, hr⟩ := low x
    exact hr.mono hb.le
  · intro β eq _
    exact (hlim.succ_ne β eq.symm).elim
  · intro sq
    refine ⟨sumSeed_realizes P (fun i => aleph (e i).1) (aleph α) (aleph0_le_aleph _) ?_ ?_ ?_⟩
    · exact fun i => Cardinal.aleph_le_aleph.mpr (e i).2.le
    · intro c h
      rw [Cardinal.aleph_limit hlim]
      apply ciSup_le
      intro β
      obtain ⟨i, rfl⟩ := onto β
      exact h i
    · exact fun i => Classical.choice ((S i).realizes (sq.restrict (e i).2.le))

/-- At every countable ordinal the concrete recursion produces a countable
seed, its rank bounds, and the conditional large realization. -/
theorem stages (α : Ordinal.{0}) (hc : α.card ≤ ℵ₀) : Nonempty (Stage α) := by
  induction α using Ordinal.limitRecOn with
  | zero => exact ⟨stageZero⟩
  | add_one α ih =>
    exact ⟨stageSucc (Classical.choice (ih ((Ordinal.card_le_card (Order.le_succ _)).trans hc)))⟩
  | limit α hlim ih =>
    exact ⟨stageLimit hlim hc fun β hβ => ih β hβ ((Ordinal.card_le_card hβ.le).trans hc)⟩

/-- The equivalent formulation using the first uncountable ordinal. -/
theorem stages_lt_omega_one (α : Ordinal.{0}) (h : α < (aleph 1).ord) : Nonempty (Stage α) :=
  stages α (Order.lt_succ_iff.mp (by simpa only [Cardinal.succ_aleph0] using Cardinal.lt_ord.mp h))

end
end KnightModel.Transfinite
