import KnightModel.RankTwo.AtlasWalk

/-! # Prefix covariance on full successor sectors -/

namespace KnightModel.RankTwo.CoherentLadders

open Set

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
variable (upper : ∀ a : A, Ioi a ≃o Ioi o)

theorem transports_succ {p a b : J} (hpa : p < a) (hab : a ≤ b)
    (prev : ∀ i < a, i ≤ p) :
    C.transports shift o d hd upper hab = C.succSectorIso shift o d hd upper hpa hab prev := by
  classical
  let hp : ∃ q < a, ∀ i < a, i ≤ q := ⟨p, hpa, prev⟩
  have heq : hp.choose = p := le_antisymm (prev _ hp.choose_spec.1) (hp.choose_spec.2 _ hpa)
  unfold transports
  rw [dif_pos (show ∃ i, i < a from ⟨p, hpa⟩), dif_pos hp]
  have aux {p' q' : J} (e : p' = q') (h₁ : p' < a) (h₂ : q' < a)
      (k₁ : ∀ i < a, i ≤ p') (k₂ : ∀ i < a, i ≤ q') :
      C.succSectorIso shift o d hd upper h₁ hab k₁ =
        C.succSectorIso shift o d hd upper h₂ hab k₂ := by
    subst q'
    rfl
  exact aux heq _ _ _ _

/-- The native point interpreted in the common domain of normalized interval charts. -/
noncomputable def succPosition {p a : J} (hpa : p < a)
    (x : C.markedRows.sector a a) : Ioi (Word.cons o Word.root) :=
  (Word.H shift o d hd upper (C.mark a p) (C.mark a a)
    (C.mark_strictMonoOn a hpa.le le_rfl hpa)).symm ⟨x.val, x.property.2 p hpa, x.property.1⟩

theorem transports_succ_apply {p a b : J} (hpa : p < a) (hab : a ≤ b)
    (prev : ∀ i < a, i ≤ p) (x : C.markedRows.sector a a) :
    (C.transports shift o d hd upper hab x).val =
      (Word.H shift o d hd upper (C.mark b p) (C.mark b a)
        (C.mark_strictMonoOn b (hpa.le.trans hab) hab hpa)
        (C.succPosition shift o d hd upper hpa x)).val := by
  rw [C.transports_succ shift o d hd upper hpa hab prev]
  rfl

/-- Copying the two bounding marks copies every point of the entire sector. -/
theorem transports_succ_prepend {p a b c : J} (hpa : p < a) (hab : a ≤ b) (hac : a ≤ c)
    (prev : ∀ i < a, i ≤ p) (s : List A)
    (hlo : C.mark b p = Word.prepend s (C.mark c p))
    (hhi : C.mark b a = Word.prepend s (C.mark c a))
    (x : C.markedRows.sector a a) :
    (C.transports shift o d hd upper hab x).val =
      Word.prepend s (C.transports shift o d hd upper hac x).val := by
  rw [C.transports_succ_apply shift o d hd upper hpa hab prev,
    C.transports_succ_apply shift o d hd upper hpa hac prev]
  have aux (l u : Word A) (e : l = Word.prepend s (C.mark c p))
      (f : u = Word.prepend s (C.mark c a)) (h : l < u) :
      (Word.H shift o d hd upper l u h (C.succPosition shift o d hd upper hpa x)).val =
        Word.prepend s ((Word.H shift o d hd upper (C.mark c p) (C.mark c a)
          (C.mark_strictMonoOn c (hpa.le.trans hac) hac hpa))
          (C.succPosition shift o d hd upper hpa x)).val := by
    subst l
    subst u
    exact Word.H_prepend shift o d hd upper s _ _ _ _
  exact aux _ _ hlo hhi _

end KnightModel.RankTwo.CoherentLadders
