import KnightModel.MainResults
import KnightModel.RankTwo.ConcreteScott
import KnightModel.RankTwo.RankConcrete
import KnightModel.RankTwo.Spectrum

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

set_option maxHeartbeats 2000000 in
/-- There is a countable structure in a countable relational language with
singleton disjointifying rank at most two. Under square at ω₁ its Scott
sentence characterizes ℵ₂ and some singleton has rank exactly two. -/
theorem exists_rank_two_scott_characterization :
    ∃ (R : ℕ → Type) (_ : ∀ n, Countable (R n)) (M : Type) (_ : Countable M)
      (D : Scott.Model R M) (C : Presentation R M),
      (∀ x, ModelRankLE D 2 [] x) ∧
        (SquareAtOmegaOne → Characterizes D C (aleph 2) ∧ ∃ x, ¬ ModelRankLE D 1 [] x) := by
  obtain ⟨Ω, ⟨bp⟩⟩ := exists_blueprint
  letI := bp
  let I := Blueprint.Model Ω
  obtain ⟨a, ha⟩ := exists_lt (1 : Ω)
  let i : I := ⟨a, ha⟩
  letI : Nonempty I := ⟨i⟩
  letI : Countable I := inferInstanceAs (Countable {x : Ω // x < 1})
  let R := FrameRelation (BaseRelation Ω) Concrete.Name
  let M := Concrete.SmallCarrier I i
  let D : Scott.Model R M := Concrete.smallModel (Ω := Ω) i
  let C : Presentation R M := Concrete.presentation (Ω := Ω) i
  have rank (x : M) : ModelRankLE D 2 [] x := Concrete.small_rankLE_two i x
  refine ⟨R, fun _ => inferInstance, M, Concrete.countable_small (Ω := Ω) i, D, C, rank, ?_⟩
  intro hs
  have spectrum : Characterizes D C (aleph 2) :=
    characterizes_of_rank_two D C rank (square_realizes_small_scott (Ω := Ω) i hs)
  exact ⟨spectrum, exists_not_rank_one_of_characterizes D C spectrum⟩

end KnightModel.RankTwo
