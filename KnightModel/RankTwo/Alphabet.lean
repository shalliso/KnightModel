import KnightModel.Model.Cardinality
import Mathlib.Data.Finsupp.Lex
import Mathlib.SetTheory.Cardinal.Finsupp
import Mathlib.SetTheory.Cardinal.Rat

/-!
# The ordered vector alphabet of a Knight model

The colexicographic order compares the greatest index at which two finitely
supported rational vectors differ. Positive unit vectors along Knight's
increasing sequence provide the letters used to label the square walks.
-/

namespace KnightModel.RankTwo

open Cardinal

/-- Finitely supported rational vectors, ordered by their greatest differing index. -/
abbrev VectorGroup (I : Type) := Colex (I →₀ ℚ)

/-- Letters of the word order. -/
abbrev Letter (I : Type) [LinearOrder I] := {v : VectorGroup I // 0 ≤ v}

/-- The basis vector at an index, viewed as a nonnegative letter. -/
noncomputable def unitLetter {I : Type} [LinearOrder I] (i : I) : Letter I :=
  ⟨toColex (Finsupp.single i 1), by
    apply le_of_lt
    refine Finsupp.Colex.lt_iff.mpr ⟨i, ?_, ?_⟩
    · intro j hj
      simp [Finsupp.single_eq_of_ne hj.ne']
    · simp⟩

theorem unitLetter_strictMono {I : Type} [LinearOrder I] : StrictMono (@unitLetter I _) := by
  intro x y h
  change toColex (Finsupp.single x (1 : ℚ)) < toColex (Finsupp.single y (1 : ℚ))
  exact Finsupp.Colex.lt_iff.mpr ⟨y, by
    intro j hj
    simp [Finsupp.single_eq_of_ne (h.trans hj).ne', Finsupp.single_eq_of_ne hj.ne'], by
    simp [Finsupp.single_eq_of_ne h.ne']⟩

/-- The actual slot sequence for the uncountable Knight index model. -/
noncomputable def slotLetter {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] [Nonempty I]
    (hI : ¬ Countable I) : (aleph 1).ord.ToType ↪o Letter I :=
  OrderEmbedding.ofStrictMono (unitLetter ∘ KnightModel.cofinalSeq (Ω := Ω) hI)
    (unitLetter_strictMono.comp (KnightModel.cofinalSeq_strictMono hI))

/-- A Knight alphabet has at most ℵ₁ vectors. -/
theorem cardinal_vectorGroup_le_aleph_one {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] :
    #(VectorGroup I) ≤ ℵ₁ := by
  change #(I →₀ ℚ) ≤ ℵ₁
  rcases isEmpty_or_nonempty I with hI | hI
  · letI := hI
    exact (mk_le_aleph0_iff.mpr inferInstance).trans (aleph0_le_aleph 1)
  · letI := hI
    rw [mk_finsupp_of_infinite', Cardinal.mkRat]
    exact max_le (KnightModel.knightModel_card_le_aleph_one (Ω := Ω)) (aleph0_le_aleph 1)

/-- The alphabet and all its words fit into ℵ₁. -/
theorem cardinal_words_le_aleph_one {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] :
    #(List (Letter I)) ≤ ℵ₁ :=
  (mk_list_le_max _).trans (max_le (aleph0_le_aleph 1)
    ((mk_subtype_le _).trans (cardinal_vectorGroup_le_aleph_one (Ω := Ω))))

end KnightModel.RankTwo
