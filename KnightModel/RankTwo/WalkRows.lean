import KnightModel.RankTwo.WalkSquare
import KnightModel.RankTwo.Words
import KnightModel.RankTwo.Atlas

/-! # The marked word rows supplied by a coherent square sequence -/

namespace KnightModel.RankTwo.CoherentLadders

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)

/-- Use the Kleene--Brouwer order, rather than ordinary list lexicographic
order, on the recorded words. -/
noncomputable def mark (b g : J) : Word A := C.word b g

@[simp] theorem mark_self (b : J) : C.mark b b = ⊤ :=
  C.word_of_le le_rfl

theorem mark_of_lt {b g : J} (h : g < b) :
    C.mark b g = Word.cons (C.slot b g h) (C.mark (C.next b g h) g) :=
  C.word_of_lt h

/-- A marked row embeds the entire initial interval, including its endpoint. -/
theorem mark_strictMonoOn (b : J) : StrictMonoOn (C.mark b) (Set.Iic b) := by
  induction b using wellFounded_lt.induction with
  | h b ih =>
    intro x hx y hy hxy
    change y ≤ b at hy
    have hxb := hxy.trans_le hy
    rcases hy.lt_or_eq with hyb | rfl
    · have hn := C.next_mono hyb hxy.le
      rw [C.mark_of_lt hxb, C.mark_of_lt hyb, Word.cons_lt_cons_iff]
      rcases hn.lt_or_eq with hlt | he
      · exact Or.inl (C.label_strictMono b (show
          (⟨C.next b x hxb, C.next_mem hxb⟩ : C.ladder b) <
           ⟨C.next b y hyb, C.next_mem hyb⟩ from hlt))
      · refine Or.inr ⟨congrArg (C.label b) (Subtype.ext he), ?_⟩
        rw [he]
        exact ih (C.next b y hyb) (C.next_lt hyb) (hxy.le.trans (C.le_next hyb))
          (C.le_next hyb) hxy
    · rw [C.mark_of_lt hxb, C.mark_self]
      exact Word.cons_lt_root _ _

/-- Concrete input for the outer-line atlas, with no marked-row hypotheses. -/
noncomputable def markedRows : MarkedRows J (Word A) where
  mark := C.mark
  mark_self := C.mark_self
  mark_strictMonoOn := C.mark_strictMonoOn

end KnightModel.RankTwo.CoherentLadders
