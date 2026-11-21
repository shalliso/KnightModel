import KnightModel.RankTwo.WordScalar

/-! # Fold graphs on symbolic finite words

The affine interpretation uses subtraction of a head letter on each pass.
Negative letters are excluded by the input and parameter predicates.
-/

namespace KnightModel.RankTwo.Semilinear

open Word Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- Fold evaluated in ambient vector coordinates. -/
def scalarFold : List V → List V → List V
  | [], x => x
  | a :: u, [] => a :: u
  | a :: u, t :: w => if t < a then t :: w else a :: scalarFold u ((t-a) :: w)

omit [Module ℚ V] in
theorem scalarFold_map (u w : List (Letter V)) :
    scalarFold (u.map Subtype.val) (w.map Subtype.val) =
      List.map Subtype.val (through shiftLetter u w) := by
  induction u generalizing w with
  | nil => rfl
  | cons a u ih =>
    cases w with
    | nil =>
      change a.val :: u.map Subtype.val = List.map Subtype.val (through shiftLetter (a::u) root)
      rw [through_root]
      rfl
    | cons t w =>
      change (if t.val < a.val then _ else _) = List.map Subtype.val (if h : t < a then _ else _)
      by_cases h : t < a
      · rw [if_pos (show t.val < a.val from h), dif_pos h]
        rfl
      · rw [if_neg (show ¬ t.val < a.val from h), dif_neg h]
        exact congrArg (List.cons a.val) (ih ((shiftLetter a ⟨t,le_of_not_gt h⟩) :: w))

/-- Valid inputs suffice: the arithmetic fold preserves the alphabet. -/
def rawFoldGraph (u x y : List V) : Prop :=
  (∀ v ∈ u, 0 ≤ v) ∧ (∀ v ∈ x, 0 ≤ v) ∧ scalarFold u x = y

theorem rawFoldGraph_iff (u x y : List V) :
    rawFoldGraph u x y ↔ ∃ v : List (Letter V), v.map Subtype.val = u ∧
      liftWordGraph Subtype.val (fun w z : List (Letter V) => through shiftLetter v w = z) x y := by
  constructor
  · rintro ⟨hu,hx,rfl⟩
    obtain ⟨v,rfl⟩ := (exists_nonneg_word u).mpr hu
    obtain ⟨w,rfl⟩ := (exists_nonneg_word x).mpr hx
    exact ⟨v,rfl,w,through shiftLetter v w,rfl,(scalarFold_map v w).symm,rfl⟩
  · rintro ⟨v,rfl,w,_,rfl,rfl,rfl⟩
    exact ⟨(exists_nonneg_word _).mp ⟨v,rfl⟩,(exists_nonneg_word _).mp ⟨w,rfl⟩,scalarFold_map v w⟩

private def minus {k} (t a : Term V k) : Term V k := .add t (.scale (-1) a)

omit [LinearOrder V] [IsOrderedAddMonoid V] in
@[simp] private theorem eval_minus {k} (t a : Term V k) (p : Fin k → V) :
    (minus t a).eval p = t.eval p - a.eval p := by simp [minus,Term.eval,sub_eq_add_neg]

theorem def_scalarFold {k} (u x y : List (Term V k)) :
    Definable {p | scalarFold (evalWord u p) (evalWord x p) = evalWord y p} := by
  induction u generalizing x y with
  | nil => exact def_word_eq x y
  | cons a u ih =>
    cases x with
    | nil => exact def_word_eq (a::u) y
    | cons t w =>
      have low := (def_term_lt t a).inter (def_word_eq (t::w) y)
      have hi : Definable {p : Fin k → V |
          a.eval p :: scalarFold (evalWord u p) ((t.eval p - a.eval p) :: evalWord w p) = evalWord y p} := by
        cases y with
        | nil => simpa [evalWord] using (def_word_false (V := V) (k := k))
        | cons b z =>
          convert (def_term_eq a b).inter (ih ((minus t a)::w) z) using 1
          ext p
          simp [evalWord]
      convert low.union ((def_term_lt t a).compl.inter hi) using 1
      ext p
      change (if t.eval p < a.eval p then _ else _) = evalWord y p ↔
        (_ ∧ _) ∨ (¬ _ ∧ _)
      split <;> simp_all [evalWord]

theorem def_rawFoldGraph {k} (u x y : List (Term V k)) :
    Definable {p | rawFoldGraph (evalWord u p) (evalWord x p) (evalWord y p)} :=
  (def_word_nonneg u).inter ((def_word_nonneg x).inter (def_scalarFold u x y))

end KnightModel.RankTwo.Semilinear
