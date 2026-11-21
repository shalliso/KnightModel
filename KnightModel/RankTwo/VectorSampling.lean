import KnightModel.RankTwo.VectorGeometry
import KnightModel.RankTwo.SemilinearQE

/-! # Affine sampling data for Knight vector spaces -/

namespace KnightModel.RankTwo

variable {I : Type} [LinearOrder I]

theorem unitLetter_pos (i : I) : (0 : VectorGroup I) < (unitLetter i).val := by
  refine Finsupp.Colex.lt_iff.mpr ⟨i, ?_, ?_⟩
  · intro j hj
    simp [unitLetter, Finsupp.single_eq_of_ne hj.ne']
  · simp [unitLetter]

/-- The finite affine test terms used for eliminating vector quantifiers. -/
noncomputable def vectorAffineSamples (i : I) :
    Semilinear.AffineSamples (vectorSamples (unitLetter i).val (unitLetter_pos i)) where
  downOffset := -(unitLetter i).val
  upOffset := (unitLetter i).val
  down_eq _ := sub_eq_add_neg _ _
  up_eq _ := rfl
  mid_eq _ _ := rfl

end KnightModel.RankTwo
