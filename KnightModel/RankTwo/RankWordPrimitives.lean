import KnightModel.RankTwo.ProgramDefinabilityScheme
import KnightModel.RankTwo.WordFoldFormula

/-! # Semilinear graph tests for the elementary named word schemes -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I] (i : I)

private theorem ofFn_coe {n} (p : Fin n → Letter I) :
    (List.ofFn p).map Subtype.val = List.ofFn (fun j => (p j).val) := by
  rw [List.map_ofFn]
  rfl

/-- The three sets of word variables all range over the same nonnegative cone.
Once these three elementary validity tests hold the raw word predicate suffices. -/
theorem schemeDefinable_of_vector_test_length (k : WordScheme) (R : List (VectorGroup I) →
    List (VectorGroup I) → List (VectorGroup I) → Prop)
    (test : ∀ (p x y : List (Letter I)), p.length = k.arity → (k.Rel Word.shiftLetter ⟨0, le_rfl⟩ (unitLetter i)
      (zero_lt_unit i) Word.shiftOpenLetter p x y ↔
      R (p.map Subtype.val) (x.map Subtype.val) (y.map Subtype.val)))
    (sem : ∀ {m} (p x y : List (Term (VectorGroup I) m)), p.length = k.arity → Definable {z |
      R (evalWord p z) (evalWord x z) (evalWord y z)}) : SchemeDefinable i k := by
  have iff_test (v : Fin k.arity → VectorGroup I) (x y : List (VectorGroup I)) :
      liftWordGraph Subtype.val (schemeGraph i ⟨k, rfl⟩ v) x y ↔
        (∀ a ∈ List.ofFn v, 0 ≤ a) ∧ (∀ a ∈ x, 0 ≤ a) ∧ (∀ a ∈ y, 0 ≤ a) ∧ R (List.ofFn v) x y := by
    constructor
    · rintro ⟨l, r, rfl, rfl, t, ht, h⟩
      obtain rfl : v = fun j => (t j).val := funext fun j => (ht j).symm
      rw [← ofFn_coe]
      exact ⟨(exists_nonneg_word _).mp ⟨_, rfl⟩, (exists_nonneg_word _).mp ⟨l, rfl⟩,
        (exists_nonneg_word _).mp ⟨r, rfl⟩, (test _ _ _ (List.length_ofFn ..)).mp h⟩
    · rintro ⟨hv, hx, hy, h⟩
      obtain ⟨l, rfl⟩ := (exists_nonneg_word _).mpr hx
      obtain ⟨r, rfl⟩ := (exists_nonneg_word _).mpr hy
      let t : Fin k.arity → Letter I := fun j => ⟨v j, hv _ (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩
      exact ⟨l, r, rfl, rfl, t, fun _ => rfl, (test _ _ _ (List.length_ofFn ..)).mpr (by rw [ofFn_coe]; exact h)⟩
  intro m s x y
  let w := List.ofFn s
  have hd := (def_word_nonneg w).inter ((def_word_nonneg x).inter ((def_word_nonneg y).inter (sem w x y (List.length_ofFn ..))))
  obtain ⟨φ, hφ⟩ := hd
  refine ⟨φ, fun z => (iff_test _ _ _).trans ?_⟩
  simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, w, evalWord, List.map_ofFn, Function.comp_def, evalTuple] using hφ z

/-- A uniform raw test in all parameter lengths also proves definability for any fixed arity. -/
theorem schemeDefinable_of_vector_test (k : WordScheme) (R : List (VectorGroup I) →
    List (VectorGroup I) → List (VectorGroup I) → Prop)
    (test : ∀ p x y : List (Letter I), k.Rel Word.shiftLetter ⟨0, le_rfl⟩ (unitLetter i)
      (zero_lt_unit i) Word.shiftOpenLetter p x y ↔
      R (p.map Subtype.val) (x.map Subtype.val) (y.map Subtype.val))
    (sem : ∀ {m} (p x y : List (Term (VectorGroup I) m)), Definable {z |
      R (evalWord p z) (evalWord x z) (evalWord y z)}) : SchemeDefinable i k :=
  schemeDefinable_of_vector_test_length i k R (fun p x y _ => test p x y)
    (fun p x y _ => sem p x y)

private theorem coe_word_eq (x y : List (Letter I)) :
    x = y ↔ x.map Subtype.val = y.map Subtype.val :=
  (List.map_injective_iff.mpr Subtype.val_injective).eq_iff.symm

theorem schemeDefinable_id : SchemeDefinable i .id :=
  schemeDefinable_of_vector_test i .id (fun _ x y => x = y) (fun _ x y => coe_word_eq x y)
    (fun _ x y => def_word_eq x y)

theorem schemeDefinable_empty : SchemeDefinable i .empty :=
  schemeDefinable_of_vector_test i .empty (fun _ _ _ => False) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => def_word_false)

theorem schemeDefinable_prefix (n : ℕ) : SchemeDefinable i (.prefix n) := by
  apply schemeDefinable_of_vector_test i (.prefix n) (fun p x y => p ++ x = y)
  · intro p x y
    change (p ++ x = y) ↔ _
    simpa only [List.map_append] using coe_word_eq (p ++ x) y
  · intro m p x y
    exact def_word_prepend p x y

theorem schemeDefinable_through (n : ℕ) : SchemeDefinable i (.through n) := by
  apply schemeDefinable_of_vector_test i (.through n) (fun p x y => scalarFold p x = y)
  · intro p x y
    let w : List (Letter I) := Word.through (A := Word.Letter (VectorGroup I)) Word.shiftLetter p x
    have e : scalarFold (p.map Subtype.val) (x.map Subtype.val) = w.map Subtype.val :=
      scalarFold_map (V := VectorGroup I) p x
    change w = y ↔ scalarFold (p.map Subtype.val) (x.map Subtype.val) = y.map Subtype.val
    rw [e]
    exact coe_word_eq w y
  · intro m p x y
    exact def_scalarFold p x y

theorem schemeDefinable_atMost (n : ℕ) : SchemeDefinable i (.atMost n) := by
  apply schemeDefinable_of_vector_test i (.atMost n) (fun p x y =>
    @LE.le (Word (VectorGroup I)) inferInstance x p ∧ x = y)
  · intro p x y
    exact and_congr (word_map_val_le x p).symm (coe_word_eq x y)
  · intro m p x y
    exact (def_word_le x p).inter (def_word_eq x y)

theorem schemeDefinable_above (n : ℕ) : SchemeDefinable i (.above n) := by
  apply schemeDefinable_of_vector_test i (.above n) (fun p x y =>
    @LT.lt (Word (VectorGroup I)) inferInstance p x ∧ x = y)
  · intro p x y
    exact and_congr (word_map_val_lt p x).symm (coe_word_eq x y)
  · intro m p x y
    exact (def_word_lt p x).inter (def_word_eq x y)

end KnightModel.RankTwo.Concrete
