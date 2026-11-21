import KnightModel.RankTwo.ProgramDefinabilityAll
import KnightModel.RankTwo.RankWordInterval
import KnightModel.RankTwo.RankWordTail

/-! # Semilinearity for every named coordinate operation -/

namespace KnightModel.RankTwo.Concrete

variable {I : Type} [LinearOrder I]

/-- Every fixed-shape evaluation of every scheme is a semilinear predicate in
the vector parameters and in the input and output letters. -/
theorem all_scheme_definable (i : I) : ∀ k : WordScheme, SchemeDefinable i k :=
  all_schemes_of_intervals i (schemeDefinable_interval i) (schemeDefinable_tail i)

/-- Every parameter fiber of the actual transition relation is semilinear. -/
theorem definable_run (i : I) {n} (k : Name n) (c : Code i) :
    Semilinear.Definable {v : Fin n → VectorGroup I | run i k (Sum.inr ∘ v) = some c} :=
  definable_run_of_schemes i (all_scheme_definable i) k c

end KnightModel.RankTwo.Concrete
