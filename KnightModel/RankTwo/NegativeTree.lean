import KnightModel.RankTwo.NegativeTreeDiagrams
import KnightModel.RankTwo.ScottGlobalDiagrams
import KnightModel.RankTwo.ScottRestrictionProfiles

/-! # The special-tree or Kurepa-tree consequence of an arbitrary rank-two example -/

namespace KnightModel.RankTwo.Scott.Negative

open Cardinal Restriction Set

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

/-- Every countable set of parameters in a large singleton orbit supports
only countably many realized one-point Scott diagrams. -/
theorem countableDiagrams_of_rank (x : M) (rank : ModelRankLE D 2 [] x)
    (big : ℵ₁ < #(orbitFiber (F C sat) Fin.elim0 x Fin.elim0)) :
    CountableDiagrams C sat (orbitFiber (F C sat) Fin.elim0 x Fin.elim0) := by
  intro A inst g
  apply countable_range_of_scott_chains C sat x rank big g
    (diagram C sat (fun i => (g i).val))
  intro d f params chain
  have base : ([d] : List N).get = singleton d :=
    funext (Fin.cases rfl (fun j => j.elim0))
  exact SentenceLabels.chain_profiles C D E sat [d] f (by simpa only [base] using chain)
    (fun a => (g a).val) (by simpa only [base] using params)

include C sat in
/-- In ZFC, a Scott sentence of singleton rank at most two with a model of
cardinality at least ℵ₂ implies a special ω₂-Aronszajn tree or an
ω₁-Kurepa tree. The trees include the full predecessor maps and the
specializing map or the ℵ₂ distinct cofinal branches, respectively. -/
theorem special_or_kurepa_of_rank (size : aleph 2 ≤ #N)
    (rank : ∀ x, ModelRankLE D 2 [] x) :
    Nonempty SpecialTree ∨ Nonempty (CountableLevelTree.{0,0,0} omegaOneStages OmegaTwo) :=
  tree_alternative_of_diagrams C sat size rank
    (fun x big => countableDiagrams_of_rank C sat x (rank x) big)

end KnightModel.RankTwo.Scott.Negative
