import KnightModel.RankTwo.ProgramDefinabilityComplete
import KnightModel.RankTwo.RankNamedFrames

/-! # Singleton rank for the concrete small frame model -/

namespace KnightModel.RankTwo.Concrete

open Scott Semilinear

variable {I Ω : Type} [Blueprint Ω] [KnightModel I Ω]

/-- Every element of the actual small structure has singleton disjointifying
rank at most two for its full relational automorphism group. -/
theorem small_rankLE_two (i : I) (x : SmallCarrier I i) :
    ModelRankLE (smallModel (Ω := Ω) i) 2 [] x :=
  namedFrame_rankLE_two i (smallInterpretation (Ω := Ω) i) (fun _ _ => Iff.rfl)
    (run_covers_vectors i) (definable_run i) x

end KnightModel.RankTwo.Concrete
