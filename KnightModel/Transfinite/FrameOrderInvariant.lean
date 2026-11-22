import KnightModel.Transfinite.FrameOrder
import KnightModel.Transfinite.LexSignTransport
import KnightModel.Transfinite.CanonicalActions

/-! # Every automorphism preserves the concrete small frame order

The through-word name realizes evaluation as a frame endpoint. Thus only this
single named operation, its parameters, and the endpoint preorder are needed
to recover all comparisons of values under an arbitrary automorphism.
-/

namespace KnightModel.Transfinite.FrameOrder

open RankTwo RankTwo.Scott RankTwo.Concrete LexSign

section Geometric
variable {I : Type} [LinearOrder I] (i : I)
local notation "F" => Concrete.SmallFrames i

noncomputable abbrev through (w : Word (Letter I)) := throughCode Word.shiftLetter
  (⟨0,le_rfl⟩ : Letter I) (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter w

noncomputable abbrev atWord (f : F) (w : Word (Letter I)) : F :=
  (family i).actProper f (through i w)

@[simp] theorem atWord_top (f : F) (w : Word (Letter I)) :
    (atWord i f w).val.val ⊤ = f.val.val w := congrArg f.val.val (throughCode_top _ _ _ _ _ _)

theorem small_below_iff (f g : F) : (smallAction i).Below f g ↔ f.val.val ⊤ ≤ g.val.val ⊤ := by
  refine ⟨?_,(family i).restrictProper⟩
  rintro ⟨c,rfl⟩
  exact g.val.val.monotone le_top

private abbrev throughName (n : Nat) : Concrete.Name n := ⟨.through n,rfl⟩

end Geometric

variable (P : Seed)
local notation "i₀" => P.mark
local notation "I" => P.M
local notation "V" => VectorGroup I
local notation "W" => Word (Letter I)
local notation "F" => Concrete.SmallFrames i₀
local notation "T" => Transfinite.smallInterpretation P.D i₀
local notation "G" => (automorphismGroup (Transfinite.smallModel P.D i₀) : Type _)
local notation "φ" => Scott.InvariantSort.map (SuccessorAut.frameSort P)
local notation "e" => SuccessorAut.vectorOrderIso P

private theorem names_eval (f : F) {n} (t : Fin n → Letter I) : (T).Transition (throughName n)
    (atWord i₀ f (List.ofFn t)) f (Sum.inr ∘ (fun j => (t j).val)) := by
  refine ⟨through i₀ _,?_,rfl⟩
  exact (run_letters_iff i₀ _ t _).mpr (fun _ _ => Iff.rfl)

private theorem zero_fixed (g : G) : e g 0 = 0 := (SuccessorAut.vectorLinearMap P g).map_zero

private noncomputable def letterPerm (g : G) : Letter I ≃ Letter I where
  toFun a := ⟨e g a, by simpa only [zero_fixed] using (e g).monotone a.property⟩
  invFun a := ⟨(e g).symm a, (e g).le_iff_le.mp (by
    simpa only [zero_fixed,OrderIso.apply_symm_apply] using a.property)⟩
  left_inv a := Subtype.ext ((e g).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((e g).apply_symm_apply a.val)

private theorem map_atWord (g : G) (f : F) (w : W) :
    φ g (atWord i₀ f w) = atWord i₀ (φ g f) (w.map (letterPerm P g)) := by
  let t := w.get
  let t' : Fin w.length → Letter I := fun j => letterPerm P g (t j)
  have h := (T).invariant_transition Sum.inr g (φ g) ((SuccessorAut.vectorSort P).map g)
    ((SuccessorAut.frameSort P).incl_map g) ((SuccessorAut.vectorSort P).incl_map g)
    (throughName w.length) (atWord i₀ f (List.ofFn t)) f (fun j => (t j).val)
  have eqn := (T).transition_functional (throughName w.length) (φ g f)
    (Sum.inr ∘ (fun j => (t' j).val)) (h.mp (names_eval P f t)) (names_eval P (φ g f) t')
  have eqw : List.ofFn t' = w.map (letterPerm P g) := by
    change List.ofFn ((letterPerm P g) ∘ w.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  simpa only [eqw,t,List.ofFn_get] using eqn

private theorem map_end (g : G) (a b : F) :
    a.val.val ⊤ ≤ b.val.val ⊤ ↔ (φ g a).val.val ⊤ ≤ (φ g b).val.val ⊤ :=
  (small_below_iff i₀ a b).symm.trans (((T).invariant_below g (φ g)
    ((SuccessorAut.frameSort P).incl_map g) a b).trans (small_below_iff i₀ _ _))

private theorem map_value (g : G) (a b : F) (w : W) :
    a.val.val w < b.val.val w ↔
    (φ g a).val.val (w.map (letterPerm P g)) < (φ g b).val.val (w.map (letterPerm P g)) := by
  rw [lt_iff_not_ge,lt_iff_not_ge]
  apply not_congr
  simpa only [map_atWord,atWord_top] using map_end P g (atWord i₀ b w) (atWord i₀ a w)

private theorem map_point (g : G) (a b : F) (w : List V) :
    point i₀ a b w ↔ point i₀ (φ g a) (φ g b) (w.map (e g)) := by
  have eqv (u : W) : (u.map (letterPerm P g)).map Subtype.val = (u.map Subtype.val).map (e g) := by
    simp only [List.map_map]
    rfl
  constructor
  · rintro ⟨u,rfl,h⟩
    exact ⟨_,eqv u,(map_value P g a b u).mp h⟩
  · rintro ⟨v,hv,h⟩
    obtain ⟨u,rfl⟩ := List.map_surjective_iff.mpr (letterPerm P g).surjective v
    exact ⟨u,List.map_injective_iff.mpr (e g).injective ((eqv u).symm.trans hv),
      (map_value P g a b u).mpr h⟩

/-- The actual full relational automorphism group preserves the frame order. -/
theorem aut_lt_iff (g : G) (a b : F) : (order i₀).lt a b ↔ (order i₀).lt (φ g a) (φ g b) :=
  earlier_transport (e g) (φ g) (map_point P g) a b

end KnightModel.Transfinite.FrameOrder
