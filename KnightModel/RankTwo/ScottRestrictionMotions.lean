import KnightModel.RankTwo.ScottRestrictionLabels
import KnightModel.RankTwo.Restriction
import Mathlib.Data.Fintype.EquivFin

/-! # Finite elementary maps associated to Scott labels

Motions are finite correspondences between tuples of the same complete
Scott label. They need not extend to automorphisms of the target.
-/

namespace KnightModel.RankTwo.Scott.SentenceLabels

/-- An abstracted finite-tuple label system with extension and selection. -/
structure Labels (X : Type) where
  label : ∀ {n}, Tuple X n → Nat
  select : ∀ {n k} {s t : Tuple X n}, label s = label t →
    ∀ p : Fin k → Fin n, label (s ∘ p) = label (t ∘ p)
  extend : ∀ {n} {s t : Tuple X n}, label s = label t →
    ∀ x, ∃ y, label (push x s) = label (push y t)

noncomputable def scottLabels {R : ℕ → Type u} {M N : Type}
    (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D)) : Labels N where
  label := number C D E h
  select := number_select C D E h
  extend := number_extend C D E h

namespace Labels

variable {X : Type} (L : Labels X)

structure Motion where
  len : Nat
  left : Tuple X len
  right : Tuple X len
  same : L.label left = L.label right

namespace Motion

variable {L}

def Mem (f : L.Motion) (x y : X) : Prop := ∃ i, f.left i = x ∧ f.right i = y

def Fixes (f : L.Motion) (B : List X) : Prop := ∀ b ∈ B, f.Mem b b

def flip (f : L.Motion) : L.Motion := ⟨f.len,f.right,f.left,f.same.symm⟩

theorem mem_flip {f : L.Motion} {x y : X} : f.flip.Mem y x ↔ f.Mem x y :=
  ⟨fun ⟨i,h,k⟩ => ⟨i,k,h⟩,fun ⟨i,h,k⟩ => ⟨i,k,h⟩⟩

/-- Restricting both correspondences to all common intermediate coordinates
composes their finite graphs without extending them globally. -/
noncomputable def comp (f g : L.Motion) : L.Motion := by
  classical
  let P := {q : Fin f.len × Fin g.len // f.right q.1 = g.left q.2}
  let z := (Fintype.equivFin P).symm
  let a (i : Fin (Fintype.card P)) := (z i).val.1
  let b (i : Fin (Fintype.card P)) := (z i).val.2
  have mid : f.right ∘ a = g.left ∘ b := funext fun i => (z i).property
  exact ⟨Fintype.card P,f.left ∘ a,g.right ∘ b,
    (L.select f.same a).trans (mid ▸ L.select g.same b)⟩

theorem mem_comp {f g : L.Motion} {x y z : X} (h : f.Mem x y) (k : g.Mem y z) :
    (f.comp g).Mem x z := by
  classical
  obtain ⟨a,ha,hy⟩ := h
  obtain ⟨b,hb,hz⟩ := k
  let P := {q : Fin f.len × Fin g.len // f.right q.1 = g.left q.2}
  let w : P := ⟨(a,b),hy.trans hb.symm⟩
  refine ⟨(Fintype.equivFin P) w, ?_⟩
  change f.left (((Fintype.equivFin P).symm ((Fintype.equivFin P) w)).val.1) = x ∧
    g.right (((Fintype.equivFin P).symm ((Fintype.equivFin P) w)).val.2) = z
  rw [Equiv.symm_apply_apply]
  exact ⟨ha,hz⟩

theorem extend_point (f : L.Motion) (x : X) :
    ∃ (g : L.Motion) (y : X), g.Mem x y ∧ ∀ u v, f.Mem u v → g.Mem u v := by
  obtain ⟨y,hy⟩ := L.extend f.same x
  let g : L.Motion := ⟨f.len+1,push x f.left,push y f.right,hy⟩
  exact ⟨g,y,⟨0,rfl,rfl⟩,fun _ _ ⟨i,hi,hj⟩ => ⟨i.succ,hi,hj⟩⟩

theorem same_of_mems {f : L.Motion} {n} {s t : Tuple X n} (h : ∀ i, f.Mem (s i) (t i)) :
    L.label s = L.label t := by
  classical
  let p (i : Fin n) := (h i).choose
  have hs : f.left ∘ p = s := funext fun i => (h i).choose_spec.1
  have ht : f.right ∘ p = t := funext fun i => (h i).choose_spec.2
  simpa only [hs,ht] using L.select f.same p

end Motion

/-- Equality of complete finite tuple labels over a finite pointwise-fixed base. -/
def Over (B v w : List X) : Prop :=
  ∃ f : L.Motion, f.Fixes B ∧ List.Forall₂ f.Mem v w

theorem over_refl (B v : List X) : L.Over B v v := by
  let s := B ++ v
  let f : L.Motion := ⟨s.length,s.get,s.get,rfl⟩
  have mem (x : X) (hx : x ∈ s) : f.Mem x x := by
    obtain ⟨i,hi⟩ := List.get_of_mem hx
    exact ⟨i,hi,hi⟩
  refine ⟨f,fun x hx => mem x (List.mem_append_left _ hx), ?_⟩
  exact List.forall₂_same.mpr (fun x hx => mem x (List.mem_append_right _ hx))

theorem over_symm {B v w : List X} (h : L.Over B v w) : L.Over B w v := by
  obtain ⟨f,hf,hw⟩ := h
  exact ⟨f.flip,fun x hx => Motion.mem_flip.mpr (hf x hx),hw.flip.imp (fun _ _ => Motion.mem_flip.mpr)⟩

theorem over_trans {B u v w : List X} (h : L.Over B u v) (k : L.Over B v w) : L.Over B u w := by
  obtain ⟨f,hf,hv⟩ := h
  obtain ⟨g,hg,hw⟩ := k
  refine ⟨f.comp g,fun x hx => Motion.mem_comp (hf x hx) (hg x hx), ?_⟩
  induction hv generalizing w with
  | nil => cases hw; exact .nil
  | cons h hv ih =>
    cases hw with
    | cons k hw => exact .cons (Motion.mem_comp h k) (ih hw)

def overSetoid (B : List X) : Setoid (List X) where
  r := L.Over B
  iseqv := ⟨L.over_refl B,L.over_symm,L.over_trans⟩

theorem over_forgetHead {B u v : List X} {a b : X} (h : L.Over B (a::u) (b::v)) : L.Over B u v := by
  obtain ⟨f,hf,h⟩ := h
  cases h with
  | cons _ h => exact ⟨f,hf,h⟩

theorem over_liftHead {B u v : List X} (h : L.Over B u v) (a : X) : ∃ b, L.Over B (a::u) (b::v) := by
  obtain ⟨f,hf,h⟩ := h
  obtain ⟨g,b,hb,ext⟩ := f.extend_point a
  exact ⟨b,g,fun x hx => ext _ _ (hf x hx),.cons hb (h.imp ext)⟩

theorem over_length {B u v : List X} (h : L.Over B u v) : u.length = v.length := by
  obtain ⟨_,_,h⟩ := h
  exact h.length_eq

end Labels
end KnightModel.RankTwo.Scott.SentenceLabels
