import KnightModel.RankTwo.WordSchemes
import KnightModel.RankTwo.WordPrograms

/-! # Evaluation identities for the coordinate schemes

The two summands of the complementary-tail recursion are presented as spans.
This removes the ordered-sum types from coordinates used to evaluate the schemes.
-/

namespace KnightModel.RankTwo.Word

open Set

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- The open tail on a single letter, viewed as a relation from the basic tail. -/
def SingleGraph (a : A) (x y : Word A) : Prop :=
  ∃ z : Ioi (cons o root), x = z.val ∧ y = ((singletonTail (upper a)).symm z).val

/-- The complementary-tail relation, including its domain. -/
def TailGraph (v x y : Word A) : Prop :=
  ∃ h : v ≠ root, ∃ z : Ioi (cons o root), x = z.val ∧
    y = (tailIso shift o d hd upper v h z).val

theorem tailGraph_singleton (a : A) (x y : Word A) :
    TailGraph shift o d hd upper (cons a root) x y ↔ SingleGraph o upper a x y := by
  constructor
  · rintro ⟨_,z,h,k⟩
    exact ⟨z,h,k⟩
  · rintro ⟨z,h,k⟩
    exact ⟨by simp [cons,root],z,h,k⟩

/-- The first copy of the basic tail in its absorption is a single-letter fold. -/
theorem absorb_inl (z : Ioi (cons o root)) :
    ((absorbTail shift hd (upper d)) (toLex (Sum.inl z))).val =
      through shift (cons d root) z.val := rfl

/-- The second copy of the basic tail is its translation above the higher letter. -/
theorem absorb_inr (z : Ioi (cons o root)) :
    ((absorbTail shift hd (upper d)) (toLex (Sum.inr z))).val =
      ((singletonTail (upper d)).symm z).val := rfl

theorem tailIso_inl (a b : A) (w : Word A) (z : Ioi (cons o root)) :
    (tailIso shift o d hd upper (cons a (cons b w)) (by simp [cons,root])
      ((absorbTail shift hd (upper d)) (toLex (Sum.inl z)))).val =
    cons a (tailIso shift o d hd upper (cons b w) (by simp [cons,root]) z).val := by
  change ((absorbTail shift hd (upper d)).symm.trans _ ((absorbTail shift hd (upper d)) _) : Ioi (cons a (cons b w))).val = _
  rw [OrderIso.trans_apply, OrderIso.symm_apply_apply]
  rfl

theorem tailIso_inr (a b : A) (w : Word A) (z : Ioi (cons o root)) :
    (tailIso shift o d hd upper (cons a (cons b w)) (by simp [cons,root])
      ((absorbTail shift hd (upper d)) (toLex (Sum.inr z)))).val =
    ((singletonTail (upper a)).symm z).val := by
  change ((absorbTail shift hd (upper d)).symm.trans _ ((absorbTail shift hd (upper d)) _) : Ioi (cons a (cons b w))).val = _
  rw [OrderIso.trans_apply, OrderIso.symm_apply_apply]
  rfl

/-- The graph for a longer endpoint is the union of two spans. Each uses only
a one-letter chart and the graph for the shorter endpoint. -/
theorem tailGraph_cons (a b : A) (w x y : Word A) :
    TailGraph shift o d hd upper (cons a (cons b w)) x y ↔
      (∃ t z : Word A, through shift (cons d root) t = x ∧
        TailGraph shift o d hd upper (cons b w) t z ∧ cons a z = y) ∨
      (∃ t : Word A, SingleGraph o upper d t x ∧ SingleGraph o upper a t y) := by
  constructor
  · rintro ⟨_, z, rfl, rfl⟩
    obtain ⟨q,rfl⟩ := (absorbTail shift hd (upper d)).surjective z
    cases hq : ofLex q with
    | inl t =>
      obtain rfl : q = toLex (.inl t) := congrArg toLex hq
      refine .inl ⟨t.val, _, (absorb_inl shift o d hd upper t).symm,
        ⟨by simp [cons,root], t, rfl, rfl⟩, (tailIso_inl shift o d hd upper a b w t).symm⟩
    | inr t =>
      obtain rfl : q = toLex (.inr t) := congrArg toLex hq
      exact .inr ⟨t.val, ⟨t,rfl,absorb_inr shift o d hd upper t⟩,
        ⟨t,rfl,tailIso_inr shift o d hd upper a b w t⟩⟩
  · rintro (⟨_,_,rfl,⟨_,t,rfl,rfl⟩,rfl⟩ | ⟨_,⟨t,rfl,rfl⟩,⟨t',ht',rfl⟩⟩)
    · exact ⟨by simp [cons,root], _, (absorb_inl shift o d hd upper t).symm,
        (tailIso_inl shift o d hd upper a b w t).symm⟩
    · obtain rfl : t = t' := Subtype.ext ht'
      exact ⟨by simp [cons,root], _, (absorb_inr shift o d hd upper t).symm,
        (tailIso_inr shift o d hd upper a b w t).symm⟩

/-- An interval with endpoints v, u is a folded complementary tail. -/
theorem interval_graph (v u : Word A) (h : v < u) (x y : Word A) :
    (∃ z : Ioi (cons o root), x = z.val ∧ y = (intervalIso shift o d hd upper h z).val) ↔
      ∃ t z : Word A, through shift u t = v ∧
        TailGraph shift o d hd upper t x z ∧ through shift u z = y := by
  let e := throughIso shift u
  let t := e.symm ⟨v, h.le⟩
  have ht : through shift u t = v := congrArg (fun w : Iic u => w.val)
    (e.apply_symm_apply ⟨v,h.le⟩)
  have hne : t ≠ root := by
    intro hr
    rw [hr, through_root] at ht
    exact h.ne ht.symm
  constructor
  · rintro ⟨z,rfl,rfl⟩
    exact ⟨t,_,ht,⟨hne,z,rfl,rfl⟩,rfl⟩
  · rintro ⟨s,_,hs,⟨_,z,rfl,rfl⟩,rfl⟩
    obtain rfl : s = t := (strictMono_through shift u).injective (hs.trans ht.symm)
    exact ⟨z,rfl,rfl⟩

@[simp] theorem singleGraph_root (a : A) (y : Word A) :
    SingleGraph o upper a root y ↔ y = root := by
  constructor
  · rintro ⟨z,h,rfl⟩
    obtain rfl : z = (⟨root, cons_lt_root o root⟩ : Ioi (cons o root)) := Subtype.ext h.symm
    rfl
  · rintro rfl
    exact ⟨⟨root,cons_lt_root o root⟩,rfl,rfl⟩

theorem singleGraph_cons (a t : A) (w y : Word A) :
    SingleGraph o upper a (cons t w) y ↔
      ∃ h : o < t, y = cons (((upper a).symm ⟨t,h⟩).val) w := by
  have f (z : Ioi (cons o root)) (hz : z.val = cons t w) :
      ∃ h : o < t, ((singletonTail (upper a)).symm z).val =
          cons (((upper a).symm ⟨t,h⟩).val) w := by
    have h : o < t := singleton_lt_cons_iff.mp (hz ▸ z.2)
    refine ⟨h, ?_⟩
    have e : z = ⟨cons t w,singleton_lt_cons_iff.mpr h⟩ := Subtype.ext hz
    rw [e]
    change (if h : o < t then _ else _) = _
    rw [dif_pos h]
  constructor
  · rintro ⟨z,h,rfl⟩
    exact f z h.symm
  · rintro ⟨h,rfl⟩
    let z : Ioi (cons o root) := ⟨cons t w,singleton_lt_cons_iff.mpr h⟩
    exact ⟨z,rfl,(f z rfl).choose_spec.symm⟩

theorem length_through_le (u x : Word A) :
    List.length (through shift u x) ≤ List.length x + List.length u := by
  induction u generalizing x with
  | nil => simp [through]
  | cons a u ih =>
    cases x with
    | nil =>
      change List.length (cons a (through shift u root)) ≤ 0 + (List.length u + 1)
      rw [through_root]
      simp [cons]
    | cons t w =>
      by_cases ht : t < a
      · simp [through,foldStep,ht,cons]
      · change List.length (if h : t < a then _ else _ : Word A) ≤ _
        rw [dif_neg ht]
        have h := ih (cons ((shift a) ⟨t,le_of_not_gt ht⟩) w)
        change List.length (through shift u _) + 1 ≤ w.length + 1 + (List.length u + 1)
        simpa [cons, Nat.add_assoc] using Nat.succ_le_succ h

/-- The normalized interval graph, with both endpoint order and input-domain guards. -/
def HGraph (v u x y : Word A) : Prop :=
  ∃ h : v < u, ∃ z : Ioi (cons o root), x = z.val ∧ y = (H shift o d hd upper v u h z).val

theorem hgraph_common (a : A) (v u x y : Word A) :
    HGraph shift o d hd upper (cons a v) (cons a u) x y ↔
      ∃ t : Word A, HGraph shift o d hd upper v u x t ∧ cons a t = y := by
  constructor
  · rintro ⟨h,z,rfl,rfl⟩
    refine ⟨_,⟨cons_lt_cons_self.mp h,z,rfl,rfl⟩,?_⟩
    exact (H_prepend shift o d hd upper [a] v u (cons_lt_cons_self.mp h) z).symm
  · rintro ⟨_,⟨h,z,rfl,rfl⟩,rfl⟩
    exact ⟨cons_lt_cons_self.mpr h,z,rfl,(H_prepend shift o d hd upper [a] v u h z).symm⟩

theorem H_different (a b : A) (v u : Word A) (h : cons a v < cons b u) (hab : a ≠ b) :
    H shift o d hd upper (cons a v) (cons b u) h = intervalIso shift o d hd upper h := by
  change H shift o d hd upper (a :: (v : List A)) (b :: (u : List A)) _ = _
  rw [H,dif_neg hab]
  rfl

theorem H_at_root (v : Word A) (h : v < root) :
    H shift o d hd upper v root h = intervalIso shift o d hd upper h := by
  cases v with
  | nil => exact (lt_irrefl _ h).elim
  | cons a v =>
    change H shift o d hd upper (a :: v) [] _ = _
    rw [H]
    · rfl
    · intro _ _ _ _ _ _ e
      cases e

/-- No word inspected in order to retrieve a preimage has to grow past the output. -/
theorem length_le_through (u x : Word A) : List.length x ≤ List.length (through shift u x) := by
  induction u generalizing x with
  | nil => exact le_rfl
  | cons a u ih =>
    cases x with
    | nil => exact Nat.zero_le _
    | cons t w =>
      by_cases ht : t < a
      · simp [through, foldStep, ht, cons]
      · have h := ih (cons ((shift a) ⟨t,le_of_not_gt ht⟩) w)
        change w.length + 1 ≤ (if h : t < a then _ else _ : Word A).length
        rw [dif_neg ht]
        exact h.trans (Nat.le_succ _)

end KnightModel.RankTwo.Word
