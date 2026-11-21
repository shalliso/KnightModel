import KnightModel.RankTwo.NegativeTree

/-! # A cardinal bound in the absence of the two restriction-tree alternatives -/

namespace KnightModel.RankTwo.Scott

open Cardinal Restriction

/-- If there is neither a special ω₂-Aronszajn tree nor an ω₁-Kurepa
tree, every model of a countable structure's Scott sentence has size at
most ℵ₁ whenever all its singleton disjointifying ranks are at most two. -/
theorem cardinal_le_aleph_one_of_no_trees {R : ℕ → Type u} {M N : Type}
    {D : Model R M} {E : Model R N} (C : Presentation R M)
    (noSpecial : ¬ Nonempty SpecialTree)
    (noKurepa : ¬ Nonempty (CountableLevelTree.{0, 0, 0} omegaOneStages OmegaTwo))
    (rank : ∀ x, ModelRankLE D 2 [] x)
    (sat : BackAndForth.Satisfies E (C.sentence D)) : #N ≤ ℵ₁ := by
  apply Order.lt_succ_iff.mp
  rw [succ_aleph, one_add_one_eq_two]
  apply lt_of_not_ge
  intro size
  exact (Negative.special_or_kurepa_of_rank C sat size rank).elim noSpecial noKurepa

end KnightModel.RankTwo.Scott
