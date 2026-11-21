import KnightModel.RankTwo.RankWordPrimitives
import KnightModel.RankTwo.WordTailFormula

/-! # Complementary-tail atom in the concrete frame language -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I] (i : I)

/-- The exact parameter fiber of a complementary-tail chart is semilinear
on every pair of fixed input and output lengths. -/
theorem schemeDefinable_tail (n : Nat) : SchemeDefinable i (.tail n) := by
  apply schemeDefinable_of_vector_test i (.tail n)
    (rawTailGraph (unitLetter i) (zero_lt_unit i))
  · intro p x y
    exact ((rawTailGraph_map (unitLetter i) (zero_lt_unit i) p _ _).trans
      (liftWordGraph_map Subtype.val_injective _ x y)).symm
  · intro k p x y
    exact def_rawTailGraph (Definable.exists_head (vectorAffineSamples i))
      (unitLetter i) (zero_lt_unit i) p x y

end KnightModel.RankTwo.Concrete
