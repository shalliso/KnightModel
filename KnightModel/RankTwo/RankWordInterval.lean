import KnightModel.RankTwo.RankWordPrimitives
import KnightModel.RankTwo.WordHFormula

/-! # The interval macro in the named semilinear scheme language -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I] (i : I)

/-- Split the fixed parameter shape into its two endpoint words, and apply
the semilinear formula for the entire interval chart to those endpoints. -/
theorem schemeDefinable_interval (m n : ℕ) : SchemeDefinable i (.interval m n) := by
  apply schemeDefinable_of_vector_test i (.interval m n) (fun p x y =>
    rawHGraph (unitLetter i) (zero_lt_unit i) (p.take m) (p.drop m) x y)
  · intro p x y
    have h := (rawHGraph_map (V := VectorGroup I) (unitLetter i) (zero_lt_unit i)
      (p.take m) (p.drop m) x y).symm
    simp only [List.map_take, List.map_drop] at h
    exact h
  · intro k p x y
    simpa only [evalWord, List.map_take, List.map_drop] using
      def_rawHGraph (Definable.exists_head (vectorAffineSamples i))
        (unitLetter i) (zero_lt_unit i) (p.take m) (p.drop m) x y

end KnightModel.RankTwo.Concrete
