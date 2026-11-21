import KnightModel.RankTwo.WordSchemes
import Mathlib.Order.Hom.Lex

/-! # Gluing the required change of anchor

The two proper initial coordinates below may have different endpoints. Their forced
change of coordinates on the lower interval extends by an independently chosen tail
isomorphism. For the concrete word order the tails are matched by the word charts.
-/

namespace KnightModel.RankTwo.Scott

open Set

variable {W : Type*} [LinearOrder W]

/-- Paste order isomorphisms on the two sides of a cut. -/
def pasteAt {x y : W} (lo : Iic x ≃o Iic y) (hi : Ioi x ≃o Ioi y) : W ≃o W :=
  (OrderIso.sumLexIicIoi x).symm.trans
    ((lo.sumLexCongr hi).trans (OrderIso.sumLexIicIoi y))

theorem pasteAt_lower {x y : W} (lo : Iic x ≃o Iic y) (hi : Ioi x ≃o Ioi y)
    (w : Iic x) : pasteAt lo hi w = (lo w).val := by
  unfold pasteAt
  simp only [OrderIso.trans_apply, OrderIso.sumLexIicIoi_symm_apply_Iic]
  exact OrderIso.sumLexIicIoi_apply_inl _

theorem pasteAt_upper {x y : W} (lo : Iic x ≃o Iic y) (hi : Ioi x ≃o Ioi y)
    (w : Ioi x) : pasteAt lo hi w = (hi w).val := by
  unfold pasteAt
  simp only [OrderIso.trans_apply, OrderIso.sumLexIicIoi_symm_apply_Ioi]
  exact OrderIso.sumLexIicIoi_apply_inr _

/-- The equation needed to keep the old frame when solving for the new upper one. -/
theorem pasteAt_factor {x y : W} (h : W ≃o Iic x) (k : W ≃o Iic y)
    (hi : Ioi x ≃o Ioi y) (w : W) :
    pasteAt (h.symm.trans k) hi (h w).val = (k w).val := by
  rw [pasteAt_lower, OrderIso.trans_apply, OrderIso.symm_apply_apply]

variable {A : Type*} [LinearOrder A]

/-- For the actual word coordinates only nonroot endpoints are required.
The tail map is supplied by the explicit word construction. -/
noncomputable def wordReanchor
    (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)
    {x y : Word A} (hx : x ≠ Word.root) (hy : y ≠ Word.root)
    (h : Word A ≃o Iic x) (k : Word A ≃o Iic y) : Word A ≃o Word A :=
  pasteAt (h.symm.trans k)
    ((Word.tailIso shift o d hd upper x hx).symm.trans (Word.tailIso shift o d hd upper y hy))

theorem wordReanchor_apply
    (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)
    {x y : Word A} (hx : x ≠ Word.root) (hy : y ≠ Word.root)
    (h : Word A ≃o Iic x) (k : Word A ≃o Iic y) (w : Word A) :
    wordReanchor shift o d hd upper hx hy h k (h w).val = (k w).val :=
  pasteAt_factor h k _ w

/-- Closure under re-anchoring follows from the actual finite scheme grammar. -/
theorem schematic_wordReanchor
    (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)
    {x y : Word A} (hx : x ≠ Word.root) (hy : y ≠ Word.root)
    (h : Word A ≃o Iic x) (k : Word A ≃o Iic y)
    (hs : Word.Schematic shift o d hd upper (fun a b => (h a).val = b))
    (ks : Word.Schematic shift o d hd upper (fun a b => (k a).val = b)) :
    Word.Schematic shift o d hd upper
      (fun a b => wordReanchor shift o d hd upper hx hy h k a = b) := by
  let tx := Word.tailIso shift o d hd upper x hx
  let ty := Word.tailIso shift o d hd upper y hy
  apply ((hs.inv.seq ks).union ((Word.schematic_tail shift o d hd upper x).inv.seq
    (Word.schematic_tail shift o d hd upper y))).congr
  intro a b
  constructor
  · rintro (⟨w, rfl, rfl⟩ | ⟨w, ⟨_, z, rfl, e⟩, ⟨_, z', ez, f⟩⟩)
    · exact wordReanchor_apply shift o d hd upper hx hy h k w
    · have zz : z = z' := Subtype.ext ez
      subst z'
      rw [e, f]
      change pasteAt _ (tx.symm.trans ty) (tx z).val = (ty z).val
      rw [pasteAt_upper, OrderIso.trans_apply, OrderIso.symm_apply_apply]
  · rintro rfl
    by_cases ha : a ≤ x
    · left
      let z : Iic x := ⟨a, ha⟩
      refine ⟨h.symm z, congrArg Subtype.val (h.apply_symm_apply z), ?_⟩
      have eq := wordReanchor_apply shift o d hd upper hx hy h k (h.symm z)
      simpa [z] using eq.symm
    · right
      let u : Ioi x := ⟨a, lt_of_not_ge ha⟩
      let z := tx.symm u
      refine ⟨z.val, ⟨hx, z, rfl, (congrArg Subtype.val (tx.apply_symm_apply u)).symm⟩,
        ⟨hy, z, rfl, ?_⟩⟩
      exact pasteAt_upper (h.symm.trans k) (tx.symm.trans ty) u

end KnightModel.RankTwo.Scott
