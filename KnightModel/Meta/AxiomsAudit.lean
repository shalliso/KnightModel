/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.MainResults
import KnightModel.RankTwo.ScottSpectrum
import KnightModel.RankTwo.Obstruction
import KnightModel.RankTwo.MarkedExtensionCriterion
import KnightModel.RankTwo.MarkedExtensionOmission
import KnightModel.RankTwo.AmalgamationObstruction
import KnightModel.RankTwo.ScottFiniteDiagrams
import Lean.Util.CollectAxioms

/-!
# Axiom Audit

This file mechanically checks that the public Knight model, rank-two spectrum and tree obstruction theorems
rely only on the three standard Lean/Mathlib foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.

The `#print axioms` commands below are run by CI and their output appears in the build log.
-/

#print axioms exists_blueprint
#print axioms knightModel_card_le_aleph_one
#print axioms exists_aleph_one_model
#print axioms nonempty_knightIso_of_encodable

#print axioms KnightModel.RankTwo.exists_rank_two_scott_characterization

#print axioms KnightModel.RankTwo.Scott.Negative.special_or_kurepa_of_rank
#print axioms KnightModel.RankTwo.Scott.cardinal_le_aleph_one_of_no_trees

#print axioms KnightModel.RankTwo.Scott.MarkedExtension.continuum_incompatible_of_large_model

#print axioms KnightModel.RankTwo.Scott.MarkedExtension.aleph_two_of_marked_family

-- Reject any additional axiom in the new results or their transitive dependencies.
run_cmd
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let results := [``KnightModel.RankTwo.exists_rank_two_scott_characterization,
    ``KnightModel.RankTwo.Scott.cardinal_le_aleph_of_scott_rank,
    ``KnightModel.RankTwo.Scott.Negative.special_or_kurepa_of_rank,
    ``KnightModel.RankTwo.Scott.cardinal_le_aleph_one_of_no_trees,
    ``KnightModel.RankTwo.Scott.countable_finite_diagrams_rank_one,
    ``KnightModel.RankTwo.Scott.countable_finite_diagrams_rank_two,
    ``KnightModel.RankTwo.Scott.MarkedExtension.continuum_incompatible_of_large_model,
    ``KnightModel.RankTwo.Scott.MarkedExtension.aleph_two_of_marked_family,
    ``KnightModel.RankTwo.Scott.MarkedExtension.Family.range_of_rank_one]
  for result in results do
    for ax in ← Lean.collectAxioms result do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {result}"
