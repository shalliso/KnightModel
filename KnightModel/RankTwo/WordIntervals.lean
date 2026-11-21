import KnightModel.RankTwo.Words
import Mathlib.Order.Hom.Set
import Mathlib.Order.Hom.Lex

/-!
# Complementary tails of word charts

The tail above a nonempty word splits at its first-letter ancestor. This identifies it
recursively with a finite ordered sum of copies of the basic tail. A fold inside the
basic tail absorbs a second copy.
-/

namespace KnightModel.RankTwo.Word

open Set

variable {A : Type*} [LinearOrder A]

private def splitTail {X : Type*} [LinearOrder X] {x y : X} (h : x < y) :
    Ioc x y ⊕ₗ Ioi y ≃o Ioi x :=
  let y' : Ioi x := ⟨y, h⟩
  let left : Ioc x y ≃o Iic y' :=
    { toFun := fun a => ⟨⟨a, a.2.1⟩, a.2.2⟩
      invFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let right : Ioi y ≃o Ioi y' :=
    { toFun := fun a => ⟨⟨a, h.trans a.2⟩, a.2⟩
      invFun := fun a => ⟨a.1.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  (left.sumLexCongr right).trans (OrderIso.sumLexIicIoi y')

/-- Restrict a chart to the open tail above one input point. -/
def underTail {X Y : Type*} [LinearOrder X] [LinearOrder Y] {u : Y}
    (e : X ≃o Iic u) (v : X) : Ioi v ≃o Ioc (e v).1 u where
  toFun w := ⟨(e w.1).1, e.strictMono w.2, (e w.1).2⟩
  invFun w := ⟨e.symm ⟨w.1, w.2.2⟩, by
    apply e.lt_iff_lt.mp
    rw [e.apply_symm_apply]
    exact w.2.1⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv w := by
    apply Subtype.ext
    exact congrArg (fun q : Iic u => q.1) (e.apply_symm_apply ⟨w.1, w.2.2⟩)
  map_rel_iff' := e.le_iff_le

@[simp] theorem singleton_lt_cons_iff {a t : A} {w : Word A} :
    cons a root < cons t w ↔ a < t := by
  simp only [cons_lt_cons_iff, not_lt_of_ge (le_root w), and_false, or_false]

private def relabelHead (a b : A) (e : Ioi a ≃o Ioi b) : Word A → Word A
  | [] => root
  | t :: w => if h : a < t then cons (e ⟨t, h⟩).1 w else root

private theorem relabelHead_above {a b : A} (e : Ioi a ≃o Ioi b)
    {x : Word A} (hx : cons a root < x) : cons b root < relabelHead a b e x := by
  cases x with
  | nil => exact cons_lt_root _ _
  | cons t w =>
    have ht := singleton_lt_cons_iff.mp hx
    simp only [relabelHead, dif_pos ht]
    exact singleton_lt_cons_iff.mpr (e ⟨t, ht⟩).2

private theorem relabelHead_strict {a b : A} (e : Ioi a ≃o Ioi b)
    {x y : Word A} (hx : cons a root < x) (hy : cons a root < y) (hxy : x < y) :
    relabelHead a b e x < relabelHead a b e y := by
  cases x with
  | nil => exact (not_lt_of_ge (le_root y) hxy).elim
  | cons s x =>
    have hs := singleton_lt_cons_iff.mp hx
    cases y with
    | nil => simp [relabelHead, hs]
    | cons t y =>
      have ht := singleton_lt_cons_iff.mp hy
      simp only [relabelHead, dif_pos hs, dif_pos ht, cons_lt_cons_iff]
      rcases cons_lt_cons_iff.mp hxy with h | ⟨rfl, h⟩
      · exact .inl (e.strictMono (show (⟨s, hs⟩ : Ioi a) < ⟨t, ht⟩ from h))
      · exact .inr ⟨rfl, h⟩

private theorem relabelHead_inv {a b : A} (e : Ioi a ≃o Ioi b)
    {x : Word A} (hx : cons a root < x) :
    relabelHead b a e.symm (relabelHead a b e x) = x := by
  cases x with
  | nil => rfl
  | cons t w =>
    have ht := singleton_lt_cons_iff.mp hx
    change relabelHead b a e.symm (if h : a < t then _ else _) = _
    rw [dif_pos ht]
    change (if h : b < (e ⟨t, ht⟩).1 then _ else _) = _
    have he : b < (e ⟨t, ht⟩).1 := (e ⟨t, ht⟩).2
    rw [dif_pos he]
    exact congrArg (fun z : Ioi a => cons z.1 w) (e.symm_apply_apply ⟨t, ht⟩)

/-- Changing the first letter identifies the tails above two singleton words. -/
def singletonTail {a b : A} (e : Ioi a ≃o Ioi b) :
    Ioi (cons a root) ≃o Ioi (cons b root) where
  toFun x := ⟨relabelHead a b e x, relabelHead_above e x.2⟩
  invFun y := ⟨relabelHead b a e.symm y, relabelHead_above e.symm y.2⟩
  left_inv x := Subtype.ext (relabelHead_inv e x.2)
  right_inv y := Subtype.ext (relabelHead_inv e.symm y.2)
  map_rel_iff' := by
    intro x y
    constructor
    · exact fun h => le_of_not_gt (fun h' => (not_lt_of_ge h) (relabelHead_strict e y.2 x.2 h'))
    · intro h
      rcases lt_or_eq_of_le h with h | rfl
      · exact le_of_lt (relabelHead_strict e x.2 y.2 h)
      · exact le_rfl

/-- Inserting a common head identifies an upper tail with the part below that head's root. -/
noncomputable def consSlice (a : A) (u : Word A) :
    Ioi u ≃o Ioc (cons a u) (cons a root) :=
  let f (x : Ioi u) : Ioc (cons a u) (cons a root) :=
    ⟨cons a x, cons_lt_cons_self.mpr x.2, cons_le_cons_self.mpr (le_root _)⟩
  StrictMono.orderIsoOfSurjective f (fun _ _ h => cons_lt_cons_self.mpr h) (by
    rintro ⟨z, h₁, h₂⟩
    cases z with
    | nil => exact (not_le_of_gt (cons_lt_root a root) h₂).elim
    | cons b w =>
      rcases cons_le_cons_iff.mp h₂ with hba | ⟨rfl, _⟩
      · rcases cons_lt_cons_iff.mp h₁ with hab | ⟨rfl, _⟩
        · exact (not_lt_of_gt hba hab).elim
        · exact (lt_irrefl _ hba).elim
      · exact ⟨⟨w, cons_lt_cons_self.mp h₁⟩, rfl⟩)

/-- `J + J ≃ J` by cutting the basic tail at a higher letter. -/
noncomputable def absorbTail
    (shift : ∀ a : A, Ici a ≃o A) {o d : A} (hd : o < d)
    (upper : Ioi d ≃o Ioi o) :
    Ioi (cons o root) ⊕ₗ Ioi (cons o root) ≃o Ioi (cons o root) := by
  let e := throughIso shift (cons d root)
  have he : (e (cons o root)).1 = cons o root := by
    change (if h : o < d then _ else _) = _
    rw [dif_pos hd]
  let left := (underTail e (cons o root)).trans
    (OrderIso.setCongr _ _ (congrArg (fun w => Ioc w (cons d root)) he))
  exact (left.sumLexCongr (singletonTail upper).symm).trans
    (splitTail (cons_lt_cons_iff.mpr (.inl hd)))

/-- Every tail above a nonempty word is isomorphic to the basic upper tail. -/
noncomputable def tailIso
    (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o) :
    (v : Word A) → v ≠ root → Ioi (cons o root) ≃o Ioi v
  | [], h => (h rfl).elim
  | a :: [], _ => (singletonTail (upper a)).symm
  | a :: b :: w, _ =>
    let child := tailIso shift o d hd upper (cons b w) (by simp [cons, root])
    let left := child.trans (consSlice a (cons b w))
    let right := (singletonTail (upper a)).symm
    (absorbTail shift hd (upper d)).symm.trans <|
      (left.sumLexCongr right).trans <|
        splitTail (cons_lt_cons_self.mpr (cons_lt_root b w))

/-- All nonempty bounded intervals open on the left are charts of the same basic tail. -/
noncomputable def intervalIso
    (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o) {v u : Word A} (h : v < u) :
    Ioi (cons o root) ≃o Ioc v u := by
  let e := throughIso shift u
  let z := e.symm ⟨v, h.le⟩
  have hz : (e z).1 = v := congrArg Subtype.val (e.apply_symm_apply ⟨v, h.le⟩)
  have hroot : z ≠ root := by
    intro heq
    rw [heq] at hz
    change through shift u root = v at hz
    exact h.ne (hz ▸ (through_root shift u))
  exact (tailIso shift o d hd upper z hroot).trans <|
    (underTail e z).trans <| OrderIso.setCongr _ _ (congrArg (fun w => Ioc w u) hz)

/-- Prefixing identifies the two intervals, including all their interior points. -/
noncomputable def prependInterval (s : List A) (v u : Word A) :
    Ioc v u ≃o Ioc (prepend s v) (prepend s u) :=
  let f (x : Ioc v u) : Ioc (prepend s v) (prepend s u) :=
    ⟨prepend s x, (prepend_lt_prepend_iff s).mpr x.2.1,
      (prepend_le_prepend_iff s).mpr x.2.2⟩
  StrictMono.orderIsoOfSurjective f (fun _ _ h => (prepend_lt_prepend_iff s).mpr h) (by
    rintro ⟨z, h₁, h₂⟩
    obtain ⟨y, rfl⟩ := exists_prepend_of_between s h₁.le h₂
    exact ⟨⟨y, (prepend_lt_prepend_iff s).mp h₁, (prepend_le_prepend_iff s).mp h₂⟩, rfl⟩)

/-- Normalized interval chart: before applying the interval construction, remove all
letters shared by the two endpoints. -/
noncomputable def H (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o) :
    (v u : Word A) → v < u → Ioi (cons o root) ≃o Ioc v u
  | a :: v, b :: u, h => if hab : a = b then by
      subst b
      exact (H shift o d hd upper v u (cons_lt_cons_self.mp h)).trans (prependInterval [a] v u)
    else intervalIso shift o d hd upper h
  | _, _, h => intervalIso shift o d hd upper h

/-- The normalized interval chart commutes exactly with a common prefix. -/
theorem H_prepend (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o) (s : List A) (v u : Word A)
    (h : v < u) (x : Ioi (cons o root)) :
    ((H shift o d hd upper (prepend s v) (prepend s u) ((prepend_lt_prepend_iff s).mpr h)) x).1 =
      prepend s ((H shift o d hd upper v u h) x).1 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [prepend_cons]
    have hs := (prepend_lt_prepend_iff s).mpr h
    have he : H shift o d hd upper (cons a (prepend s v)) (cons a (prepend s u))
        (cons_lt_cons_self.mpr hs) =
        (H shift o d hd upper (prepend s v) (prepend s u) hs).trans
          (prependInterval [a] (prepend s v) (prepend s u)) := by
      change H shift o d hd upper (a :: (prepend s v : List A)) (a :: (prepend s u : List A)) _ = _
      rw [H]
      rw [dif_pos rfl]
      rfl
    rw [he]
    exact congrArg (cons a) ih

section Alphabet
variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- Strict final segments of the nonnegative alphabet are identified by translation. -/
def shiftOpenLetter (a : Letter V) : Ioi a ≃o Ioi (⟨0, le_rfl⟩ : Letter V) where
  toFun t := ⟨⟨t.1.1 - a.1, (sub_pos.mpr t.2).le⟩, sub_pos.mpr t.2⟩
  invFun t := ⟨⟨t.1.1 + a.1, add_nonneg t.1.2 a.2⟩, lt_add_of_pos_left _ t.2⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; exact sub_add_cancel _ _
  right_inv t := by apply Subtype.ext; apply Subtype.ext; exact add_sub_cancel_right _ _
  map_rel_iff' := by
    intro s t
    change s.1.1 - a.1 ≤ t.1.1 - a.1 ↔ s.1.1 ≤ t.1.1
    exact sub_le_sub_iff_right _

end Alphabet
end KnightModel.RankTwo.Word
