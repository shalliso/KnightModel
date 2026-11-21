import KnightModel.RankTwo.ScottVectors
import KnightModel.RankTwo.WordSchemes
import Mathlib.Data.List.Forall2

/-! # Matching words over the Knight vector alphabets

All letters of a matched word use a single finite Knight condition. A witness in
a composed partial graph may require enlarging that condition.
-/

namespace KnightModel.RankTwo.Scott

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]

abbrev LetterMatch (p : ModelIsoCondition I J Ω) (a : Letter I) (b : Letter J) :=
  VectorMatch p a.val b.val

abbrev WordMatch (p : ModelIsoCondition I J Ω) (x : Word (Letter I)) (y : Word (Letter J)) :=
  List.Forall₂ (LetterMatch p) x y

namespace WordMatch

variable {p q : ModelIsoCondition I J Ω}
variable {s x : Word (Letter I)} {t y : Word (Letter J)}

theorem keep (H : WordMatch p x y) (h : q ≤ p) : WordMatch q x y :=
  List.Forall₂.imp (fun _ _ v => v.keep h) H

theorem symm (H : WordMatch p x y) : WordMatch p.symm y x := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.symm ih

theorem forth [Nonempty J] (p : ModelIsoCondition I J Ω) (x : Word (Letter I)) :
    ∃ (q : ModelIsoCondition I J Ω) (y : Word (Letter J)), q ≤ p ∧ WordMatch q x y := by
  induction x with
  | nil => exact ⟨p, [], le_rfl, .nil⟩
  | cons i w ih =>
    obtain ⟨q, w', qp, hw⟩ := ih
    obtain ⟨r, j, rq, hj⟩ := VectorMatch.forth q i.val
    have pos : 0 ≤ j := (VectorMatch.zero.le_iff hj).mp i.property
    exact ⟨r, ⟨j,pos⟩ :: w', rq.trans qp, .cons hj (hw.keep rq)⟩

theorem back [Nonempty I] (p : ModelIsoCondition I J Ω) (y : Word (Letter J)) :
    ∃ (q : ModelIsoCondition I J Ω) (x : Word (Letter I)), q ≤ p ∧ WordMatch q x y := by
  obtain ⟨q, x, hq, h⟩ := forth p.symm y
  exact ⟨q.symm, x, by simpa using (ModelIsoCondition.symm_le_symm_iff.mpr hq), h.symm⟩

private theorem letter_eq {a c : Letter I} {b d : Letter J}
    (h : LetterMatch p a b) (k : LetterMatch p c d) : a = c ↔ b = d :=
  Subtype.ext_iff.trans ((h.eq_iff k).trans Subtype.ext_iff.symm)

theorem lt_iff (H : WordMatch p s t) (K : WordMatch p x y) : s < x ↔ t < y := by
  induction H generalizing x y with
  | nil =>
    cases K with
    | nil => exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    | cons => exact iff_of_false (not_lt_of_ge (Word.le_root _)) (not_lt_of_ge (Word.le_root _))
  | @cons a b s t h _ ih =>
    cases K with
    | nil => exact iff_of_true (Word.cons_lt_root _ _) (Word.cons_lt_root _ _)
    | @cons c d x y k w =>
      change Word.cons a s < Word.cons c x ↔ Word.cons b t < Word.cons d y
      rw [Word.cons_lt_cons_iff, Word.cons_lt_cons_iff]
      exact (h.lt_iff k).or ((letter_eq h k).and (ih w))

theorem le_iff (H : WordMatch p s t) (K : WordMatch p x y) : s ≤ x ↔ t ≤ y := by
  rw [← not_lt, ← not_lt, K.lt_iff H]

theorem eq_iff (H : WordMatch p s t) (K : WordMatch p x y) : s = x ↔ t = y := by
  rw [le_antisymm_iff, le_antisymm_iff, H.le_iff K, K.le_iff H]

theorem prepend (H : WordMatch p s t) (K : WordMatch p x y) :
    WordMatch p (Word.prepend s x) (Word.prepend t y) := List.rel_append H K

/-- The subtract-and-fold charts commute with transport of the rational coefficients. -/
theorem through (H : WordMatch p s t) (K : WordMatch p x y) :
    WordMatch p (Word.through Word.shiftLetter s x) (Word.through Word.shiftLetter t y) := by
  induction H generalizing x y with
  | nil => exact K
  | @cons a b s t ab _ ih =>
    cases K with
    | nil => exact .cons ab (ih .nil)
    | @cons i j x y ij xy =>
      have same : i < a ↔ j < b := ij.lt_iff ab
      by_cases hi : i < a
      · simp only [Word.through, Word.foldStep, dif_pos hi, dif_pos (same.mp hi)]
        exact .cons ij xy
      · have hj : ¬ j < b := fun h => hi (same.mpr h)
        simp only [Word.through, Word.foldStep, dif_neg hi, dif_neg hj]
        exact .cons ab (ih (.cons (ij.sub ab) xy))

end WordMatch
end KnightModel.RankTwo.Scott
