/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.MainResults
import KnightModel.RankTwo.ScottSpectrum
import Mathlib.Util.AssertNoSorry

/-!
# Axiom Audit

This file mechanically checks that the public Knight model and rank-two spectrum theorems
rely only on the three standard Lean/Mathlib foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.

The `#print axioms` commands below are run by CI and their output appears in the build log.
-/

#print axioms exists_blueprint
#print axioms knightModel_card_le_aleph_one
#print axioms exists_aleph_one_model
#print axioms nonempty_knightIso_of_encodable

#print axioms KnightModel.RankTwo.exists_rank_two_scott_characterization

-- Reject a new axiom anywhere in the proof of the rank-two construction.
run_cmd
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let used ← Lean.collectAxioms ``KnightModel.RankTwo.exists_rank_two_scott_characterization
  for ax in used do
    unless allowed.contains ax do
      throwError "Unexpected axiom in rank-two construction: {ax}"
