import KnightModel.RankTwo.WalkSquare
import KnightModel.RankTwo.Alphabet
import KnightModel.RankTwo.AtlasCardinal
import KnightModel.RankTwo.AtlasWalk

/-!
# The square atlas on a Knight alphabet

Specialize the walk rows and all three sector transports to the ordered
rational vector group on an actual uncountable Knight model. The resulting
line has size ℵ₂. Its cofinal marked points have principal initial segments
isomorphic to the word order.
-/

namespace KnightModel.RankTwo

open Cardinal Set

/-- Indices of the outer line. This small type, unlike the set of ordinals
below ω₂ viewed as a subtype of all ordinals, lives in the carrier universe. -/
abbrev OuterIndex : Type := (aleph 2).ord.ToType

noncomputable section

variable {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] [Nonempty I]

/-- The marks use positions on a club as subscripts for positive unit vectors. -/
def knightLadders (S : SquareLadders OuterIndex (aleph 1).ord) (hI : ¬ Countable I) :
    CoherentLadders OuterIndex (Letter I) :=
  S.labelled (Ordinal.ToType.mk.toOrderEmbedding.trans (slotLetter (Ω := Ω) hI))

/-- In the Knight alphabet every closed and open letter tail has the
translation isomorphism used by the folds. -/
def knightTransports (S : SquareLadders OuterIndex (aleph 1).ord)
    (hI : ¬ Countable I) (i : I) : (knightLadders (Ω := Ω) S hI).markedRows.Transports :=
  (knightLadders (Ω := Ω) S hI).transports Word.shiftLetter ⟨0, le_rfl⟩ (unitLetter i)
    (by
      change (0 : VectorGroup I) < toColex (Finsupp.single i 1)
      refine Finsupp.Colex.lt_iff.mpr ⟨i, ?_, ?_⟩
      · intro j hj
        simp [Finsupp.single_eq_of_ne hj.ne']
      · simp) Word.shiftOpenLetter

/-- The principal segments of the actual outer line over an uncountable Knight
index order. -/
theorem squareAtlas_on (S : SquareLadders OuterIndex (aleph 1).ord) (hunc : ¬ Countable I) :
    ∃ (X : Type) (_ : LinearOrder X), #X = aleph 2 ∧
      ∃ a : OuterIndex ↪o X, (∀ x, ∃ b, x ≤ a b) ∧
        ∀ b, Nonempty (Iic (a b) ≃o Word (Letter I)) := by
  let C := knightLadders (Ω := Ω) S hunc
  let D := C.markedRows
  let q : D.Transports := knightTransports (Ω := Ω) S hunc (Classical.choice ‹Nonempty I›)
  have wordBound : #(Word (Letter I)) ≤ aleph 2 :=
    (cardinal_words_le_aleph_one (Ω := Ω)).trans (aleph_le_aleph.mpr (one_le_two : (1 : Ordinal) ≤ 2))
  refine ⟨D.Outer, inferInstance, D.mk_outer_omega_two wordBound,
    OrderEmbedding.ofStrictMono D.anchor D.anchor_strictMono, ?_, fun b => ⟨D.chart q b⟩⟩
  intro x
  exact ⟨D.index x, D.le_anchor_iff.mpr le_rfl⟩

end
end KnightModel.RankTwo
