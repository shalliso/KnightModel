import KnightModel.RankTwo.AtlasChange
import KnightModel.RankTwo.ScottFrames

/-! # The frame action on an actual atlas

Frames are actual order embeddings into the outer line obtained by composing
a chart with an allowed coordinate. Equal functions give equal frames even
when their enclosing charts and program parameters differ.
-/

namespace KnightModel.RankTwo

/-- The whole-domain coordinate programs, as extensional maps on words.
Restriction divides two programs whose endpoints are in the indicated order;
pasting extends the forced isomorphism between two proper initial intervals. -/
structure CoordinateFamily (W : Type*) [LinearOrder W] [OrderTop W] where
  allowed : Set (W ↪o W)
  id_mem : ((OrderIso.refl W).toOrderEmbedding) ∈ allowed
  comp_mem : ∀ {h k}, h ∈ allowed → k ∈ allowed → k.trans h ∈ allowed
  restrict : ∀ {f g : W ↪o W}, f ∈ allowed → g ∈ allowed → f ⊤ ≤ g ⊤ →
    ∃ h ∈ allowed, ∀ w, g (h w) = f w
  paste : ∀ {h k : W ↪o W}, h ∈ allowed → k ∈ allowed → h ⊤ < ⊤ → k ⊤ < ⊤ →
    ∃ l ∈ allowed, ∀ w, l (h w) = k w

namespace CoordinateFamily

variable {W : Type*} [LinearOrder W] [OrderTop W] (C : CoordinateFamily W)

abbrev Code := {f : W ↪o W // f ∈ C.allowed}

def one : C.Code := ⟨(OrderIso.refl W).toOrderEmbedding, C.id_mem⟩

def comp (h k : C.Code) : C.Code := ⟨k.val.trans h.val, C.comp_mem h.property k.property⟩

end CoordinateFamily

namespace MarkedRows

variable {J W : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder W] [OrderTop W]
variable (D : MarkedRows J W) (q : D.Transports) (C : CoordinateFamily W)

def Frames := { f : W ↪o D.Outer // ∃ b : J, ∃ c : C.Code,
    ∀ w, f w = ((D.chart q b).symm (c.val w)).val }

noncomputable def present (b : J) (c : C.Code) : D.Frames q C :=
  ⟨OrderEmbedding.ofStrictMono (fun w => ((D.chart q b).symm (c.val w)).val)
    (fun _ _ h => (D.chart q b).symm.strictMono (c.val.strictMono h)), b, c, fun _ => rfl⟩

theorem present_surjective : Function.Surjective
    (fun p : J × C.Code => D.present q C p.1 p.2) := by
  intro f
  obtain ⟨b,c,h⟩ := f.property
  exact ⟨(b,c), Subtype.ext (DFunLike.ext _ _ (fun w => (h w).symm))⟩

noncomputable def frameAnchor (b : J) : D.Frames q C := D.present q C b C.one

@[simp] theorem frameAnchor_top (b : J) : (D.frameAnchor q C b).val ⊤ = D.anchor b := by
  change ((D.chart q b).symm ⊤).val = D.anchor b
  have h := D.chart_anchor q (le_refl b)
  rw [D.mark_self] at h
  exact congrArg Subtype.val ((D.chart q b).symm_apply_eq.mpr h.symm)

theorem frameAnchor_injective : Function.Injective (D.frameAnchor q C) := by
  intro a b h
  apply D.anchor_strictMono.injective
  simpa only [D.frameAnchor_top] using congrArg (fun f : D.Frames q C => f.val ⊤) h

noncomputable def actFrame (f : D.Frames q C) (k : C.Code) : D.Frames q C :=
  ⟨k.val.trans f.val, by
    obtain ⟨b,c,h⟩ := f.property
    exact ⟨b, C.comp c k, fun w => h (k.val w)⟩⟩

/-- Moving to a larger enclosing chart changes the presenting code, and
retains exactly the same embedding into the outer line. -/
theorem present_change {a b : J} (hab : a ≤ b) (change_mem : D.change q hab ∈ C.allowed)
    (k : C.Code) : D.present q C a k = D.present q C b (C.comp ⟨_,change_mem⟩ k) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro w
  let x := (D.chart q a).symm (k.val w)
  have h : D.chart q b (D.includeInitial hab x) = D.change q hab (k.val w) := by
    rw [← D.change_chart]
    simp only [x, OrderIso.apply_symm_apply]
  exact (congrArg Subtype.val ((D.chart q b).symm_apply_eq.mpr h.symm)).symm

variable (allowed_change : ∀ {a b : J} (hab : a ≤ b), D.change q hab ∈ C.allowed)

include allowed_change in
/-- Every two frames have presentations in the same enclosing chart. -/
theorem common_presentation (f g : D.Frames q C) : ∃ b : J, ∃ h k : C.Code,
    f = D.present q C b h ∧ g = D.present q C b k := by
  obtain ⟨⟨a,h⟩, rfl⟩ := D.present_surjective q C f
  obtain ⟨⟨b,k⟩, rfl⟩ := D.present_surjective q C g
  exact ⟨max a b, _, _, D.present_change q C (le_max_left _ _) (allowed_change _) h,
    D.present_change q C (le_max_right _ _) (allowed_change _) k⟩

private theorem realize_restriction {b : J} {h k e : C.Code}
    (eqn : ∀ w, h.val (e.val w) = k.val w) :
    D.actFrame q C (D.present q C b h) e = D.present q C b k :=
  Subtype.ext (DFunLike.ext _ _ (fun w => congrArg (fun z => ((D.chart q b).symm z).val) (eqn w)))

include allowed_change in
theorem below_frame {f g : D.Frames q C} (h : f.val ⊤ ≤ g.val ⊤) :
    ∃ x : C.Code, D.actFrame q C g x = f := by
  obtain ⟨b,k,l,rfl,rfl⟩ := D.common_presentation q C allowed_change f g
  have h' : k.val ⊤ ≤ l.val ⊤ :=
    (D.chart q b).symm.le_iff_le.mp h
  obtain ⟨e, he, hold⟩ := C.restrict k.property l.property h'
  exact ⟨⟨e,he⟩, D.realize_restriction q C hold⟩

include allowed_change in
/-- The frame endpoint order is precisely factorization by a permitted coordinate. -/
theorem below_frame_iff {f g : D.Frames q C} :
    f.val ⊤ ≤ g.val ⊤ ↔ ∃ x : C.Code, D.actFrame q C g x = f := by
  refine ⟨D.below_frame q C allowed_change, ?_⟩
  rintro ⟨x,rfl⟩
  exact g.val.monotone le_top

theorem proper_of_below_frame {f g : D.Frames q C} {h : C.Code}
    (e : D.actFrame q C g h = f) (ht : f.val ⊤ < g.val ⊤) : h.val ⊤ < ⊤ := by
  subst f
  exact g.val.lt_iff_lt.mp ht

/-- The coordinate and frame action used in the frame back-and-forth, now
on the genuine frame sort of the lexicographic sum. -/
noncomputable def frameAction [NoMaxOrder J] : Scott.FrameAction C.Code (D.Frames q C) where
  one := C.one
  comp := C.comp
  act := D.actFrame q C
  proper h := h.val ⊤ < ⊤
  act_one _ := Subtype.ext (DFunLike.ext _ _ (fun _ => rfl))
  act_comp _ _ _ := Subtype.ext (DFunLike.ext _ _ (fun _ => rfl))
  compare u v := by
    rcases le_or_gt (v.val ⊤) (u.val ⊤) with h | h
    · exact Or.inl (D.below_frame q C allowed_change h)
    · obtain ⟨k,hk⟩ := D.below_frame q C allowed_change h.le
      exact Or.inr ⟨k,D.proper_of_below_frame q C hk h,hk⟩
  higher u := by
    obtain ⟨b,hb⟩ := exists_gt (D.index (u.val ⊤))
    have hg : u.val ⊤ < (D.frameAnchor q C b).val ⊤ := by
      rw [D.frameAnchor_top]
      exact (D.le_anchor_iff.mpr (le_refl _)).trans_lt (D.anchor_strictMono hb)
    obtain ⟨k,hk⟩ := D.below_frame q C allowed_change hg.le
    exact ⟨D.frameAnchor q C b,k,D.proper_of_below_frame q C hk hg,hk⟩
  paste h k hh hk := by
    obtain ⟨l,hl,he⟩ := C.paste h.property k.property hh hk
    exact ⟨⟨l,hl⟩, Subtype.ext (DFunLike.ext _ _ he)⟩

end MarkedRows
end KnightModel.RankTwo
