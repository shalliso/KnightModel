import KnightModel.RankTwo.RestrictionCardinal
import KnightModel.RankTwo.RankOrdinal

/-!
# The cardinal spectrum of a finite-rank Scott sentence

When an ℵ₂-model exists, the rank-two cardinal bound determines its maximum
model size and forces the singleton rank bound to be sharp.
-/

namespace KnightModel.RankTwo.Scott

open Cardinal

universe w

/-- Disjointifying rank over a finite parameter set for the full automorphism group. -/
noncomputable def ModelOrdinalRankLE {R : ℕ → Type} {M : Type} (D : Model R M)
    (α : Ordinal.{0}) (B : Finset M) (x : M) : Prop := by
  classical
  exact OrdinalRankLE ↥(automorphismGroup D) α B x

theorem modelOrdinalRankLE_nat_empty {R : ℕ → Type} {M : Type} (D : Model R M) (n : ℕ) (x : M) :
    ModelOrdinalRankLE D n ∅ x ↔ ModelRankLE D n [] x := by
  classical
  exact ordinalRankLE_empty_iff (G := ↥(automorphismGroup D)) n x

variable {R : ℕ → Type} {M : Type} (D : Model R M) (C : Presentation R M)

/-- The Scott sentence has a model of exactly κ elements and every one of its
models has size at most κ. -/
def Characterizes (κ : Cardinal.{0}) : Prop :=
  (∃ (N : Type) (E : Model R N), #N = κ ∧ BackAndForth.Satisfies E (C.sentence D)) ∧
    ∀ (N : Type w) (E : Model R N), BackAndForth.Satisfies E (C.sentence D) → #N ≤ lift.{w} κ

theorem characterizes_of_rank_two (rank : ∀ x, ModelRankLE D 2 [] x)
    (realized : ∃ (N : Type) (E : Model R N),
      #N = aleph 2 ∧ BackAndForth.Satisfies E (C.sentence D)) :
    Characterizes.{w} D C (aleph 2) :=
  ⟨realized, fun _ _ h => by simpa using cardinal_le_aleph_of_scott_rank C 2 rank h⟩

/-- A countable structure whose sentence characterizes ℵ₂ cannot have every
singleton of disjointifying rank at most one. -/
theorem exists_not_rank_one_of_characterizes (spectrum : Characterizes.{w} D C (aleph 2)) :
    ∃ x, ¬ ModelRankLE D 1 [] x := by
  classical
  by_contra! h
  obtain ⟨N, E, he, hs⟩ := spectrum.1
  have small := cardinal_le_aleph_of_scott_rank C 1 h hs
  rw [he] at small
  simp at small

end KnightModel.RankTwo.Scott
