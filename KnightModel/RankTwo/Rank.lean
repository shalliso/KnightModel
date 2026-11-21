import Mathlib.Algebra.Group.Action.Defs

/-!
# Finite disjointifying rank for a permutation action

These are the natural-number stages of the disjointifying rank in §4.2 of Shaun
Allison's *Classification Strength of Polish Groups: Involving S∞*.  Parameters
are a finite list.  Taking the group to be the automorphism group of a structure
gives its singleton rank.  One can compute upper bounds in an invariant sort and
transport them to the whole structure using `rankLE_of_equivariant_embedding`.
-/

namespace KnightModel.RankTwo

variable {G X Y : Type*} [Group G] [MulAction G X]

/-- The pointwise stabilizer condition for a finite parameter list. -/
def Fixes (g : G) (B : List X) : Prop := ∀ b ∈ B, g • b = b

/-- Conjugacy by an automorphism fixing the parameters pointwise. -/
def Conjugate (G : Type*) [Group G] [MulAction G X] (B : List X) (x y : X) : Prop :=
  ∃ g : G, Fixes g B ∧ g • x = y

/-- The finite stages of the disjointifying rank. At a successor the first
disjunct is the witness clause and the second is the comparison clause. -/
def RankLE (G : Type*) [Group G] [MulAction G X] : ℕ → List X → X → Prop
  | 0, B, x => ∀ g : G, Fixes g B → g • x = x
  | n + 1, B, x =>
    (∃ c : X, ∀ c', Conjugate G B c c' → RankLE G n (c' :: B) x) ∨
    (∀ y, Conjugate G B x y → RankLE G n (y :: B) x ∨ RankLE G n (x :: B) y)

@[simp] theorem fixes_nil (g : G) : Fixes g ([] : List X) := by
  simp [Fixes]

@[simp] theorem fixes_cons (g : G) (a : X) (B : List X) :
    Fixes g (a :: B) ↔ g • a = a ∧ Fixes g B := by
  simp [Fixes]

/-- Adjoining parameters preserves an upper bound. -/
theorem RankLE.mono_params {n : ℕ} {B C : List X} {x : X}
    (h : RankLE G n B x) (hBC : ∀ b ∈ B, b ∈ C) : RankLE G n C x := by
  induction n generalizing B C x with
  | zero => exact fun g hg => h g fun b hb => hg b (hBC b hb)
  | succ n ih =>
    have restrict {a b : X} : Conjugate G C a b → Conjugate G B a b := by
      rintro ⟨g, hg, hx⟩
      exact ⟨g, fun q hq => hg q (hBC q hq), hx⟩
    have prepend (a : X) : ∀ b ∈ a :: B, b ∈ a :: C := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hBC b hb)
    rcases h with ⟨a, ha⟩ | hc
    · exact Or.inl ⟨a, fun b hb => ih (ha b (restrict hb)) (prepend b)⟩
    · exact Or.inr fun y hy =>
        (hc y (restrict hy)).imp (fun hx => ih hx (prepend y)) (fun hx => ih hx (prepend x))

/-- The predicates really are cumulative upper bounds. -/
theorem RankLE.succ {n : ℕ} {B : List X} {x : X} (h : RankLE G n B x) :
    RankLE G (n + 1) B x :=
  Or.inr fun y _ => Or.inl (h.mono_params fun _ => List.mem_cons_of_mem y)

section Embedding

variable [MulAction G Y] (f : X → Y) (inj : Function.Injective f)
    (equiv : ∀ (g : G) (x : X), f (g • x) = g • f x)

include inj equiv

private theorem fixes_map_iff (g : G) (B : List X) :
    Fixes g (B.map f) ↔ Fixes g B := by
  constructor
  · intro hg b hb
    apply inj
    rw [equiv]
    exact hg _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  · intro hg b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rw [← equiv, hg a ha]

/-- A bound proved for the restricted action on one sort also holds in the
ambient action. In particular witnesses from the sort remain available. -/
theorem rankLE_of_equivariant_embedding {n : ℕ} {B : List X} {x : X}
    (h : RankLE G n B x) : RankLE G n (B.map f) (f x) := by
  induction n generalizing B x with
  | zero =>
    intro g hg
    rw [← equiv, h g ((fixes_map_iff f inj equiv g B).mp hg)]
  | succ n ih =>
    rcases h with ⟨a, ha⟩ | hc
    · refine Or.inl ⟨f a, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      rw [← equiv]
      exact ih (ha (g • a) ⟨g, (fixes_map_iff f inj equiv g B).mp hg, rfl⟩)
    · apply Or.inr
      rintro _ ⟨g, hg, rfl⟩
      rw [← equiv]
      exact (hc (g • x) ⟨g, (fixes_map_iff f inj equiv g B).mp hg, rfl⟩).imp
        (fun hx => ih (B := (g • x) :: B) (x := x) hx)
        (fun hx => ih (B := x :: B) (x := g • x) hx)

end Embedding

end KnightModel.RankTwo
