import KnightModel.RankTwo.AtlasChange
import KnightModel.RankTwo.WalkRows
import KnightModel.RankTwo.WalkPieces
import KnightModel.RankTwo.WordIntervals

/-! # Realizing the sector transports by word operations -/

namespace KnightModel.RankTwo

open Set

/-- Insert a prefix, with a possible extra fold at its final boundary. -/
structure TailShape (A : Type*) where
  prefix : List A
  extra : Option A

namespace TailShape

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A)

def endWord (h : TailShape A) : Word A := h.extra.toList

def apply (h : TailShape A) (w : Word A) : Word A :=
  Word.prepend h.prefix (Word.through shift h.endWord w)

def embedding (h : TailShape A) : Word A ↪o Word A :=
  OrderEmbedding.ofStrictMono (h.apply shift)
    (fun _ _ hlt => (Word.prepend_lt_prepend_iff _).mpr
      (Word.strictMono_through shift _ hlt))

theorem convex (h : TailShape A) {u v w : Word A}
    (hl : h.embedding shift u ≤ w) (hr : w ≤ h.embedding shift v) :
    w ∈ Set.range (h.embedding shift) := by
  obtain ⟨z, hz⟩ := Word.exists_prepend_of_between h.prefix hl hr
  have hzu : z ≤ Word.through shift h.endWord v :=
    (Word.prepend_le_prepend_iff _).mp (hz ▸ hr)
  have hv : Word.through shift h.endWord v ≤ h.endWord :=
    (Word.range_through shift _ _).mp ⟨v, rfl⟩
  obtain ⟨x, hx⟩ := (Word.range_through shift _ _).mpr (hzu.trans hv)
  exact ⟨x, (congrArg (Word.prepend h.prefix) hx).trans hz⟩

end TailShape

namespace CoherentLadders

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)

def Fits (b a : J) (h : TailShape A) : Prop :=
  C.CopiesTail b a h.prefix ∧ C.word b a = h.prefix ++ h.extra.toList ∧
    ∀ t ∈ h.extra, ∀ i (hi : i < a), C.slot a i hi < t

theorem exists_shape {b a : J} (hab : a ≤ b) (pos : ∃ i, i < a) :
    ∃ h : TailShape A, C.Fits b a h := by
  obtain ⟨s, hs, endpoint | ⟨t, endpoint, below⟩⟩ := C.tail hab pos
  · exact ⟨⟨s, none⟩, hs, by simpa using endpoint, by simp⟩
  · exact ⟨⟨s, some t⟩, hs, endpoint, by simpa using below⟩

noncomputable def shape {b a : J} (hab : a ≤ b) (pos : ∃ i, i < a) : TailShape A :=
  (C.exists_shape hab pos).choose

theorem shape_fits {b a : J} (hab : a ≤ b) (pos : ∃ i, i < a) :
    C.Fits b a (C.shape hab pos) := (C.exists_shape hab pos).choose_spec

/-- Prefix and final letter are both forced at a limit. -/
theorem fits_unique {b a : J} {h k : TailShape A}
    (hlim : ∀ n < a, ∃ i, n < i ∧ i < a) (hh : C.Fits b a h) (hk : C.Fits b a k) :
    h = k := by
  have hp := C.copiesTail_unique hlim hh.1 hk.1
  obtain ⟨s, e⟩ := h
  obtain ⟨t, f⟩ := k
  change s = t at hp
  subst t
  have he : e.toList = f.toList := List.append_cancel_left (hh.2.1.symm.trans hk.2.1)
  cases e <;> cases f <;> simp_all

variable (shift : ∀ a : A, Ici a ≃o A)

theorem shape_apply_mark {b a i : J} {h : TailShape A}
    (hh : C.Fits b a h) (hi : i < a) :
    h.apply shift (C.mark a i) = Word.prepend h.prefix (C.mark a i) := by
  apply congrArg (Word.prepend h.prefix)
  cases he : h.extra with
  | none => simp [TailShape.endWord, he, Word.through]
  | some t =>
    have hlt := hh.2.2 t (by simp [he]) i hi
    rw [C.mark_of_lt hi]
    simp [TailShape.endWord, he, Word.through, Word.foldStep, Word.cons, hlt]

/-- Below any earlier native mark the optional fold acts identically, including
on all the unmarked words inside that sector. -/
theorem shape_apply_of_le_mark {b a i : J} {h : TailShape A}
    (hh : C.Fits b a h) (hi : i < a) (w : Word A) (hw : w ≤ C.mark a i) :
    h.apply shift w = Word.prepend h.prefix w := by
  apply congrArg (Word.prepend h.prefix)
  cases he : h.extra with
  | none => simp [TailShape.endWord, he, Word.through]
  | some t =>
    have hlt := hh.2.2 t (by simp [he]) i hi
    rw [C.mark_of_lt hi] at hw
    cases w with
    | nil => exact (not_le_of_gt (Word.cons_lt_root _ _) hw).elim
    | cons k w =>
      have hkt : k < t := by
        rcases Word.cons_le_cons_iff.mp hw with h | ⟨h, _⟩
        · exact h.trans hlt
        · exact h ▸ hlt
      simp [TailShape.endWord, he, Word.through, Word.foldStep, hkt]

noncomputable def limitSectorIso {b a : J} (hab : a ≤ b) (pos : ∃ i, i < a)
    (hlim : ∀ n < a, ∃ i, n < i ∧ i < a) (h : TailShape A) (hh : C.Fits b a h) :
    C.markedRows.sector a a ≃o C.markedRows.sector b a :=
  C.markedRows.sectorIsoOfCofinal hab pos (h.embedding shift) (h.convex shift) (by
    change h.apply shift (C.mark a a) = C.mark b a
    rw [C.mark_self]
    change Word.prepend h.prefix (Word.through shift h.endWord Word.root) = C.mark b a
    rw [Word.through_root]
    exact hh.2.1.symm) (by
      intro i hi
      obtain ⟨n, hn, hcopy⟩ := hh.1
      obtain ⟨j, hmj, hja⟩ := hlim (max n i) (max_lt hn hi)
      refine ⟨j, (le_max_right _ _).trans hmj.le, hja, ?_⟩
      change h.apply shift (C.mark a j) = C.mark b j
      rw [C.shape_apply_mark shift hh hja]
      exact (hcopy j ((le_max_left _ _).trans_lt hmj) hja).symm)

noncomputable def firstSectorIso {a b : J} (hfirst : ∀ i, ¬i < a) :
    C.markedRows.sector a a ≃o C.markedRows.sector b a :=
  let source : C.markedRows.sector a a ≃o Word A := {
    toFun := Subtype.val
    invFun := fun w => ⟨w, ⟨by change w ≤ C.mark a a; rw [C.mark_self]; exact le_top,
      fun i hi => (hfirst i hi).elim⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  (source.trans (Word.throughIso shift (C.mark b a))).trans
    (OrderIso.setCongr _ _ (C.markedRows.sector_eq_Iic_of_first hfirst).symm)

variable (o d : A) (hd : o < d) (upper : ∀ a : A, Ioi a ≃o Ioi o)

noncomputable def succSectorIso {p a b : J} (hpa : p < a) (hab : a ≤ b)
    (prev : ∀ i < a, i ≤ p) : C.markedRows.sector a a ≃o C.markedRows.sector b a :=
  let source := OrderIso.setCongr _ _ (C.markedRows.sector_eq_Ioc_of_predecessor hpa le_rfl prev)
  let target := OrderIso.setCongr _ _ (C.markedRows.sector_eq_Ioc_of_predecessor hpa hab prev)
  let h₀ := C.mark_strictMonoOn a hpa.le le_rfl hpa
  let h₁ := C.mark_strictMonoOn b (hpa.le.trans hab) hab hpa
  ((source.trans (Word.H shift o d hd upper _ _ h₀).symm).trans
    (Word.H shift o d hd upper _ _ h₁)).trans target.symm

theorem interior_of_no_previous {a : J} (hp : ¬∃ p < a, ∀ i < a, i ≤ p) :
    ∀ n < a, ∃ i, n < i ∧ i < a := by
  intro n hn
  by_contra h
  exact hp ⟨n, hn, fun i hi => le_of_not_gt (fun hni => h ⟨i, hni, hi⟩)⟩

/-- Every sector in every row gets an actual transport constructed from its marks. -/
noncomputable def transports : C.markedRows.Transports := by
  classical
  intro a b hab
  exact if hn : ∃ i, i < a then
    if hp : ∃ p < a, ∀ i < a, i ≤ p then
      C.succSectorIso shift o d hd upper hp.choose_spec.1 hab hp.choose_spec.2
    else
      C.limitSectorIso shift hab hn (interior_of_no_previous hp) (C.shape hab hn) (C.shape_fits hab hn)
  else C.firstSectorIso shift (fun i hi => hn ⟨i, hi⟩)

end CoherentLadders
end KnightModel.RankTwo
