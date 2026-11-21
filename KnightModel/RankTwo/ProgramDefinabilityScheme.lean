import KnightModel.RankTwo.ProgramDefinabilityConcrete

namespace KnightModel.RankTwo.Concrete

open Semilinear

/-- The fixed-shape semilinearity contract of a parameter-free word scheme. -/
abbrev SchemeDefinable {I : Type} [LinearOrder I] (i : I) (k : WordScheme) : Prop :=
  LiftDefinable Subtype.val (schemeGraph i ⟨k,rfl⟩)

end KnightModel.RankTwo.Concrete
