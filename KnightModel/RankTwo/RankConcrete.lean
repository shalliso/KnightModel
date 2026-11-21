import KnightModel.RankTwo.ProgramDefinabilityConcrete
import KnightModel.RankTwo.RankNamedFrames

/-! # Singleton rank for the concrete small frame model -/

namespace KnightModel.RankTwo.Concrete

open Scott Semilinear

variable {I Ω : Type} [Blueprint Ω] [KnightModel I Ω]

/-- The remaining input from the word programs is exactly the semilinearity
of the fiber presenting a prescribed concrete coordinate. -/
theorem small_rankLE_two_of_run_definable (i : I)
    (definable : ∀ {n} (k : Name n) (c : Code i), Definable {p : Fin n → VectorGroup I |
      run i k (Sum.inr ∘ p) = some c}) (x : SmallCarrier I i) :
    ModelRankLE (smallModel (Ω := Ω) i) 2 [] x :=
  namedFrame_rankLE_two i (smallInterpretation (Ω := Ω) i) (fun _ _ => Iff.rfl)
    (run_covers_vectors i) definable x

/-- Concrete finite-letter tests and uniform prefix bounds imply the full
singleton rank bound, after eliminating their vector quantifiers. -/
theorem small_rankLE_two_of_scheme_semantics (i : I)
    (finiteGraph : ∀ {n} (k : Name n), LiftDefinable Subtype.val (schemeGraph i k))
    (bounded : ∀ {n} (k : Name n), ∃ b, ∀ p, PrefixBounds (schemeGraph i k p) b)
    (x : SmallCarrier I i) : ModelRankLE (smallModel (Ω := Ω) i) 2 [] x :=
  small_rankLE_two_of_run_definable i (definable_run_fiber i finiteGraph bounded) x

end KnightModel.RankTwo.Concrete
