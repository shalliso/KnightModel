import KnightModel.RankTwo.AtlasCoordinates

/-! # The proper-coordinate frame sort on the word order without its root -/

namespace KnightModel.RankTwo.CoordinateFamily

variable {W : Type*} [LinearOrder W] [OrderTop W] (C : CoordinateFamily W)

/-- Actual charts on the line obtained by deleting the final word. -/
abbrev ProperFrames := {f : C.Code // f.val ⊤ < ⊤}

def actProper (f : C.ProperFrames) (h : C.Code) : C.ProperFrames :=
  ⟨C.comp f.val h, (f.val.val.monotone le_top).trans_lt f.property⟩

theorem restrictProper {f g : C.ProperFrames} (hle : f.val.val ⊤ ≤ g.val.val ⊤) :
    ∃ h : C.Code, C.actProper g h = f := by
  obtain ⟨h,hh,eqn⟩ := C.restrict f.val.property g.val.property hle
  exact ⟨⟨h,hh⟩,Subtype.ext (Subtype.ext (DFunLike.ext _ _ eqn))⟩

theorem isProper_of_actProper {f g : C.ProperFrames} {h : C.Code}
    (eqn : C.actProper g h = f) (hle : f.val.val ⊤ < g.val.val ⊤) : h.val ⊤ < ⊤ := by
  subst f
  exact g.val.val.lt_iff_lt.mp hle

/-- The concrete countable-model action. Its frame sort is a subtype of codes,
so countability follows directly from countability of the coordinate schemes. -/
def properFrameAction
    (unbounded : ∀ w : W, w < ⊤ → ∃ g : C.ProperFrames, w < g.val.val ⊤) :
    Scott.FrameAction C.Code C.ProperFrames where
  one := C.one
  comp := C.comp
  act := C.actProper
  proper h := h.val ⊤ < ⊤
  act_one _ := Subtype.ext (Subtype.ext (DFunLike.ext _ _ (fun _ => rfl)))
  act_comp _ _ _ := Subtype.ext (Subtype.ext (DFunLike.ext _ _ (fun _ => rfl)))
  compare f g := by
    rcases le_or_gt (g.val.val ⊤) (f.val.val ⊤) with hg | hf
    · exact Or.inl (C.restrictProper hg)
    · obtain ⟨h,eqn⟩ := C.restrictProper hf.le
      exact Or.inr ⟨h,C.isProper_of_actProper eqn hf,eqn⟩
  higher f := by
    obtain ⟨g,hg⟩ := unbounded _ f.property
    obtain ⟨h,eqn⟩ := C.restrictProper hg.le
    exact ⟨g,h,C.isProper_of_actProper eqn hg,eqn⟩
  paste h k hh hk := by
    obtain ⟨l,hl,he⟩ := C.paste h.property k.property hh hk
    exact ⟨⟨l,hl⟩, Subtype.ext (DFunLike.ext _ _ he)⟩

end KnightModel.RankTwo.CoordinateFamily
