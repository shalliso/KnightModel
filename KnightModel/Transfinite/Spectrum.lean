import KnightModel.Transfinite.Square
import KnightModel.Transfinite.CardinalBound

/-! # The Scott spectrum and exact disjointifying rank of the ordinal tower -/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott Cardinal

universe w
noncomputable section

variable {α : Ordinal.{0}}

private theorem singleton_le (P : Seed) {α : Ordinal.{0}} (bound : P.TupleLE α) (x : P.M) :
    ModelOrdinalRankLE P.D α ∅ x := by
  classical
  letI : DecidableEq P.M := Classical.decEq _
  have hx : ComparisonLE α (⊤ : Subgroup ↥(automorphismGroup P.D)) x :=
    (bound (fun _ : Fin 1 => x)).of_stabilizer fun g _ => by
      rw [tuple_fixed_iff]
      exact ⟨fun h => h 0,fun h _ => h⟩
  unfold ModelOrdinalRankLE
  exact (hx.restrict le_top).ordinalRankLE

private theorem singleton_lt (P : Seed) {α : Ordinal.{0}} (bound : P.TupleLT α) (x : P.M) :
    ∃ β < α, ModelOrdinalRankLE P.D β ∅ x := by
  classical
  letI : DecidableEq P.M := Classical.decEq _
  obtain ⟨β,hβ,hr⟩ := P.singletonLT bound x
  refine ⟨β,hβ,?_⟩
  unfold ModelOrdinalRankLE
  exact (hr.restrict le_top).ordinalRankLE

/-- At each cardinal stage the rank bounds alone exclude all larger Scott models,
including at a countable limit where every source tuple has a smaller rank. -/
theorem Stage.cardinal_bound (S : Stage α) {N : Type w} (E : Model S.seed.R N)
    (sat : BackAndForth.Satisfies E (S.seed.pres.sentence S.seed.D)) :
    #N ≤ lift.{w} (aleph α) := by
  by_cases hf : α < Ordinal.omega0
  · simpa only [ceilingIndex,if_pos hf] using
      cardinal_le_of_ordinal_rank S.seed.pres α (singleton_le _ S.rank) sat
  · apply cardinal_le_of_label_bounds S.seed.pres (aleph0_le_aleph _) _ sat
    intro x
    obtain ⟨β,hβ,hr⟩ := singleton_lt _ (S.strict_infinite (le_of_not_gt hf)) x
    exact ⟨β,hr,aleph_le_aleph.mpr (ceilingIndex_le_of_lt hβ)⟩

theorem Stage.characterizes (S : Stage α) (sq : SquaresBelow α) :
    Characterizes.{w} S.seed.D S.seed.pres (aleph α) := by
  obtain ⟨A⟩ := S.realizes sq
  exact ⟨⟨A.N,A.E,A.size,A.sat⟩,fun _ => S.cardinal_bound⟩

private theorem Stage.rank_at_ceiling (S : Stage (ceilingIndex α)) :
    ∀ x, ModelOrdinalRankLE S.seed.D α ∅ x := by
  by_cases hf : α < Ordinal.omega0
  · apply singleton_le
    intro n t
    simpa only [ceilingIndex,if_pos hf] using S.rank t
  · exact singleton_le _ (S.infinite_succ_rank α (if_neg hf) (le_of_not_gt hf))

theorem Stage.exact_at_ceiling (S : Stage (ceilingIndex α)) (sq : SquaresBelow (ceilingIndex α)) :
    ∃ x, ModelOrdinalRankLE S.seed.D α ∅ x ∧
      ∀ β < α, ¬ ModelOrdinalRankLE S.seed.D β ∅ x := by
  obtain ⟨A⟩ := S.realizes sq
  exact exists_exact_rank_of_realization S.seed.pres α S.rank_at_ceiling A.sat A.size

/-- Only the positive indices require a set-theoretic hypothesis. -/
theorem squaresBelow_iff_positive_square (α : Ordinal.{0}) :
    SquaresBelow α ↔ ∀ β, 0 < β → β < α → JensenSquare (aleph β) := by
  rw [squaresBelow_iff_positive]
  exact forall_congr' fun β => forall_congr' fun _ => forall_congr' fun _ =>
    (jensenSquare_iff (aleph0_le_aleph β)).symm

/-- Cardinal-indexed version. The countable model and its singleton bounds
are chosen before the hypotheses for realizing the largest model. -/
theorem exists_scott_characterizing_aleph (α : Ordinal.{0}) (hc : α < Ordinal.omega 1) :
    ∃ P : Seed, (∀ x, ModelOrdinalRankLE P.D α ∅ x) ∧
      ((∀ β, 0 < β → β < α → JensenSquare (aleph β)) → Characterizes.{w} P.D P.pres (aleph α)) := by
  obtain ⟨S⟩ := stages_lt_omega_one α (by simpa only [ord_aleph] using hc)
  exact ⟨S.seed,singleton_le _ S.rank,fun sq =>
    S.characterizes ((squaresBelow_iff_positive_square α).mpr sq)⟩

/-- Rank-indexed version. The Scott sentence attains the universal
cardinal upper bound, and one singleton excludes every smaller rank. -/
theorem exists_sharp_scott_characterization (α : Ordinal.{0}) (hc : α < Ordinal.omega 1) :
    ∃ P : Seed, (∀ x, ModelOrdinalRankLE P.D α ∅ x) ∧
      ((∀ β, 0 < β → β < ceilingIndex α → JensenSquare (aleph β)) →
        Characterizes.{w} P.D P.pres (aleph (ceilingIndex α)) ∧
        ∃ x, ∀ β < α, ¬ ModelOrdinalRankLE P.D β ∅ x) := by
  have hc' : ceilingIndex α < Ordinal.omega 1 := by
    unfold ceilingIndex
    split_ifs
    · exact hc
    · exact (isSuccLimit_omega 1).succ_lt hc
  obtain ⟨S⟩ := stages_lt_omega_one (ceilingIndex α) (by simpa only [ord_aleph] using hc')
  refine ⟨S.seed,S.rank_at_ceiling,fun sq => ?_⟩
  have ladders := (squaresBelow_iff_positive_square _).mpr sq
  obtain ⟨x,_,hx⟩ := S.exact_at_ceiling ladders
  exact ⟨S.characterizes ladders,x,hx⟩

/-- The first limit rank. The example has an ℵ_(ω+1) model, and in the
countable source a single point exceeds every finite rank. -/
theorem exists_rank_omega_scott_characterization :
    ∃ P : Seed, (∀ x, ModelOrdinalRankLE P.D Ordinal.omega0 ∅ x) ∧
      ((∀ β, 0 < β → β ≤ Ordinal.omega0 → JensenSquare (aleph β)) →
        Characterizes.{w} P.D P.pres (aleph (Ordinal.omega0 + 1)) ∧
        ∃ x, ∀ n : ℕ, ¬ ModelOrdinalRankLE P.D n ∅ x) := by
  obtain ⟨P,hr,h⟩ := exists_sharp_scott_characterization.{w} Ordinal.omega0
    Ordinal.omega0_lt_omega_one
  refine ⟨P,hr,fun sq => ?_⟩
  have eq : ceilingIndex Ordinal.omega0 = Order.succ Ordinal.omega0 := if_neg (lt_irrefl _)
  obtain ⟨spectrum,x,hx⟩ := h (fun β hp hβ => sq β hp (Order.lt_succ_iff.mp (eq ▸ hβ)))
  exact ⟨by simpa only [eq,Order.succ_eq_add_one] using spectrum,
    x,fun n => hx n (Ordinal.natCast_lt_omega0 n)⟩

end
end KnightModel.Transfinite
