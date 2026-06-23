/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.MainResults

/-!
# Axiom Audit

This file mechanically checks that the four public theorems in `KnightModel/MainResults.lean`
rely only on the three standard Lean/Mathlib foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.

The `#print axioms` commands below are run by CI and their output appears in the build log.
-/

#print axioms exists_blueprint
#print axioms knightModel_card_le_aleph_one
#print axioms exists_aleph_one_model
#print axioms nonempty_knightIso_of_encodable
