import KnightModel.RankTwo.AtlasPieces
import KnightModel.RankTwo.SquareAtlas

/-! # The actual outer line over an uncountable Knight model -/

namespace KnightModel.RankTwo

open Cardinal Set

theorem zero_lt_unit {I : Type} [LinearOrder I] (i : I) :
    (⟨0, le_rfl⟩ : Letter I) < unitLetter i := by
  change (0 : VectorGroup I) < toColex (Finsupp.single i 1)
  refine Finsupp.Colex.lt_iff.mpr ⟨i, ?_, ?_⟩
  · intro j hj
    simp [Finsupp.single_eq_of_ne hj.ne']
  · simp

variable {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] [Nonempty I]

/-- The changes on the actual Knight charts are finite unions of guarded word
operations; the ordinal indices are absent from each representing rule. -/
theorem knight_change_graph (S : SquareLadders OuterIndex (aleph 1).ord)
    (hI : ¬ Countable I) (i : I) {a b : OuterIndex} (hab : a ≤ b) :
    let C := knightLadders (Ω := Ω) S hI
    let q : C.markedRows.Transports := knightTransports (Ω := Ω) S hI i
    ∃ rs : List (GuardedRule (Letter I)), ∀ x y : Word (Letter I),
      C.markedRows.change q hab x = y ↔
      ∃ r ∈ rs, r.contains x ∧
        r.rule.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i)
          (zero_lt_unit i) Word.shiftOpenLetter x y :=
  (knightLadders (Ω := Ω) S hI).change_graph Word.shiftLetter
    ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter hab

end KnightModel.RankTwo
