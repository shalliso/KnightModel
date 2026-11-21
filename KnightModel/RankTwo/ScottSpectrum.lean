import KnightModel.MainResults
import KnightModel.RankTwo.ConcreteScott
import KnightModel.RankTwo.RestrictionCardinal

/-!
# The Scott model at the second uncountable cardinal

The original Knight construction supplies both index models. The countable
frame model and its sentence are chosen before square is assumed. Square
enters only in constructing the large realization.
-/

namespace KnightModel.RankTwo

open Cardinal Scott

/-- The fixed countable model has a Scott realization of size ℵ₂ under square. -/
theorem square_realizes_small_scott {Ω I : Type} [Blueprint Ω] [KnightModel I Ω]
    [Nonempty I] [Countable I] (i : I) (hs : SquareAtOmegaOne) :
    ∃ (N : Type) (E : Scott.Model (FrameRelation (BaseRelation Ω) Concrete.Name) N),
      #N = aleph 2 ∧ BackAndForth.Satisfies E
        ((Concrete.presentation (Ω := Ω) i).sentence (Concrete.smallModel i)) := by
  obtain ⟨J, kJ, cardJ⟩ := exists_aleph_one_model (Ω := Ω)
  letI := kJ
  have unc : ¬Countable J := by
    intro hc
    exact aleph0_lt_aleph_one.not_ge (cardJ ▸ mk_le_aleph0_iff.mpr hc)
  haveI : Nonempty J := not_isEmpty_iff.mp (fun h => unc (by letI := h; infer_instance))
  obtain ⟨p, j, _, mark⟩ := extendIndexLeft (ModelIsoCondition.empty : ModelIsoCondition I J Ω) i
  obtain ⟨S⟩ := hs
  exact ⟨Concrete.LargeCarrier (Ω := Ω) S unc j, Concrete.largeModel S unc j,
    Concrete.mk_large S unc j, Concrete.large_satisfies i j p mark S unc⟩

/-- Choose a countable language and a countable structure in ZFC. Under square
its Scott sentence has a model of cardinality exactly ℵ₂. -/
theorem exists_square_scott_realization :
    ∃ (R : ℕ → Type) (_ : ∀ n, Countable (R n)) (M : Type) (_ : Countable M)
      (D : Scott.Model R M) (C : Presentation R M),
      SquareAtOmegaOne → ∃ (N : Type) (E : Scott.Model R N),
        #N = aleph 2 ∧ BackAndForth.Satisfies E (C.sentence D) := by
  obtain ⟨Ω, ⟨bp⟩⟩ := exists_blueprint
  letI := bp
  let I := Blueprint.Model Ω
  obtain ⟨a, ha⟩ := exists_lt (1 : Ω)
  let i : I := ⟨a, ha⟩
  letI : Nonempty I := ⟨i⟩
  letI : Countable I := inferInstanceAs (Countable {x : Ω // x < 1})
  exact ⟨_, fun _ => inferInstance, Concrete.SmallCarrier I i, Concrete.countable_small i,
    Concrete.smallModel (Ω := Ω) i, Concrete.presentation i, square_realizes_small_scott i⟩

end KnightModel.RankTwo
