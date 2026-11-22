import KnightModel.RankTwo.ScottCountable
import Mathlib.SetTheory.Cardinal.Ordinal

/-! # The ordered, pointed input to one frame construction

The countable input and its cardinal upper bound make sense independently
of a square sequence. A large realization carries the increasing sequence
needed for the slots at the next successor.
-/

namespace KnightModel.Transfinite

open RankTwo.Scott Cardinal

structure Seed where
  R : ℕ → Type
  M : Type
  D : Model R M
  countRel : ∀ n, Countable (R n)
  countM : Countable M
  ord : LinearOrder M
  mark : M
  leSym : R 2
  le_iff : ∀ t, D leSym t ↔ t 0 ≤ t 1
  markSym : R 1
  mark_iff : ∀ t, D markSym t ↔ t 0 = mark

namespace Seed

attribute [instance] ord countRel countM

instance (P : Seed) : Nonempty P.M := ⟨P.mark⟩

noncomputable def pres (P : Seed) : Presentation P.R P.M :=
  Presentation.ofCountable P.R P.M

/-- A uniform cardinal bound on the Scott models of the seed. -/
def Bounded (P : Seed) (κ : Cardinal.{0}) : Prop :=
  ∀ {N : Type} (E : Model P.R N), BackAndForth.Satisfies E (P.pres.sentence P.D) → #N ≤ κ

/-- A large realization, with the interpretation of the two distinguished
symbols and an increasing sequence of its full cardinal length. -/
structure Realizes (P : Seed) (κ : Cardinal.{0}) where
  N : Type
  E : Model P.R N
  ord : LinearOrder N
  mark : N
  le_iff : ∀ t, E P.leSym t ↔ t 0 ≤ t 1
  mark_iff : ∀ t, E P.markSym t ↔ t 0 = mark
  sat : BackAndForth.Satisfies E (P.pres.sentence P.D)
  seq : κ.ord.ToType ↪o N
  size : #N = κ

attribute [instance] Realizes.ord

end Seed
end KnightModel.Transfinite
