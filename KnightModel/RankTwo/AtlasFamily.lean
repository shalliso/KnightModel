import KnightModel.RankTwo.AtlasSmallFrames
import KnightModel.RankTwo.AtlasSchemes
import KnightModel.RankTwo.ScottPasting

/-! # The coordinate family from the countable, parameterized scheme language -/

namespace KnightModel.RankTwo

open Set

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- All extensional word-program coordinates with full initial image. -/
noncomputable def schematicFamily : CoordinateFamily (Word A) where
  allowed f := Word.Schematic shift o d hd upper (fun x y => f x = y) ∧ CoordinateFamily.FullInitial f
  id_mem := ⟨Word.schematic_id shift o d hd upper, CoordinateFamily.fullInitial_id⟩
  comp_mem := by
    intro f g hf hg
    refine ⟨(hg.1.seq hf.1).congr ?_, hg.2.comp hf.2⟩
    intro x y
    simp
  restrict := by
    intro f g hf hg hle
    refine ⟨CoordinateFamily.divide f g hg.2 hle, ⟨(hf.1.seq hg.1.inv).congr ?_,
      CoordinateFamily.fullInitial_divide f g hf.2 hg.2 hle⟩,
      CoordinateFamily.divide_apply f g hg.2 hle⟩
    exact fun x y => (CoordinateFamily.divide_graph f g hg.2 hle x y).symm
  paste := by
    intro h k hh hk hp kp
    let L := CoordinateFamily.coordIso h hh.2
    let R := CoordinateFamily.coordIso k hk.2
    let join := Scott.wordReanchor shift o d hd upper hp.ne kp.ne L R
    refine ⟨join.toOrderEmbedding, ⟨?_,?_⟩, ?_⟩
    · exact Scott.schematic_wordReanchor shift o d hd upper hp.ne kp.ne L R hh.1 hk.1
    · ext z
      constructor
      · rintro ⟨w,rfl⟩
        exact join.monotone le_top
      · exact fun _ => join.surjective z
    · exact Scott.wordReanchor_apply shift o d hd upper hp.ne kp.ne L R

/-- The elementary fold through a prescribed word is a code of the full family. -/
noncomputable def throughCode (u : Word A) : (schematicFamily shift o d hd upper).Code :=
  ⟨OrderEmbedding.ofStrictMono (Word.through shift u) (Word.strictMono_through shift u),
    Word.schematic_through shift o d hd upper u, by
      ext w
      change (∃ z, Word.through shift u z = w) ↔ w ≤ Word.through shift u Word.root
      rw [Word.through_root]
      exact Word.range_through shift u w⟩

@[simp] theorem throughCode_top (u : Word A) :
    (throughCode shift o d hd upper u).val ⊤ = u := Word.through_root shift u

theorem proper_unbounded [NoMaxOrder A] (w : Word A) (hw : w < ⊤) :
    ∃ f : (schematicFamily shift o d hd upper).ProperFrames, w < f.val.val ⊤ := by
  cases w with
  | nil => exact (lt_irrefl _ hw).elim
  | cons a w =>
    obtain ⟨b,hab⟩ := exists_gt a
    let f := throughCode shift o d hd upper (Word.cons b Word.root)
    have he : f.val ⊤ = Word.cons b Word.root := throughCode_top _ _ _ _ _ _
    refine ⟨⟨f,he ▸ Word.cons_lt_root _ _⟩, ?_⟩
    change Word.cons a w < f.val ⊤
    rw [he]
    exact Word.cons_lt_cons_iff.mpr (Or.inl hab)

noncomputable def smallFrameAction [NoMaxOrder A] :=
  (schematicFamily shift o d hd upper).properFrameAction (proper_unbounded shift o d hd upper)

variable {J : Type*} [LinearOrder J] [WellFoundedLT J] (C : CoherentLadders J A)

theorem CoherentLadders.change_allowed {b c : J} (hbc : b ≤ c) :
    C.markedRows.change (C.transports shift o d hd upper) hbc ∈
      (schematicFamily shift o d hd upper).allowed := by
  refine ⟨C.schematic_change shift o d hd upper hbc, ?_⟩
  have hend := C.markedRows.range_change (C.transports shift o d hd upper) hbc
  let e := C.markedRows.change (C.transports shift o d hd upper) hbc
  have e_top : e ⊤ = C.mark c b := by
    apply le_antisymm
    · exact (Set.ext_iff.mp hend (e ⊤)).mp ⟨⊤,rfl⟩
    · obtain ⟨v,hv⟩ := (Set.ext_iff.mp hend (C.mark c b)).mpr (show C.mark c b ≤ C.mark c b from le_rfl)
      exact hv ▸ e.monotone le_top
  exact hend.trans (congrArg Iic e_top.symm)

/-- The higher and lower moves are valid on real large frames using only the
same countable coordinate schemes employed on the small side. -/
noncomputable def CoherentLadders.largeFrameAction [NoMaxOrder J] :=
  C.markedRows.frameAction (C.transports shift o d hd upper) (schematicFamily shift o d hd upper)
    (fun hbc => C.change_allowed shift o d hd upper hbc)

end KnightModel.RankTwo
