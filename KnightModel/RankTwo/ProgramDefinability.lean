import Mathlib.Data.List.Basic

/-! # Finite graph tests for relations on prefix-rewritten words -/

namespace KnightModel.RankTwo

/-- Once both heads are long enough, the final letters must agree and can be
cancelled. The same bound controls the possible change in word length. -/
structure PrefixBounds {A : Type*} (R : List A → List A → Prop) (k : Nat) : Prop where
  sizes : ∀ {x y}, R x y → x.length ≤ y.length + k ∧ y.length ≤ x.length + k
  snoc : ∀ x y, k ≤ x.length → k ≤ y.length → ∀ a b,
    R (x ++ [a]) (y ++ [b]) ↔ a = b ∧ R x y

namespace PrefixBounds

variable {A : Type*} {R S : List A → List A → Prop} {k l : Nat}

theorem mono (h : PrefixBounds R k) (hl : k ≤ l) : PrefixBounds R l where
  sizes hxy := by obtain ⟨h₁,h₂⟩ := h.sizes hxy; constructor <;> omega
  snoc x y hx hy := h.snoc x y (Nat.le_trans hl hx) (Nat.le_trans hl hy)

theorem diag : PrefixBounds (fun x y : List A => x = y) 0 where
  sizes h := by subst_vars; simp
  snoc x y _ _ a b := by
    rw [List.append_eq_append_iff_of_size_eq_right (by simp)]
    simp [and_comm]

theorem empty : PrefixBounds (fun _ _ : List A => False) 0 where
  sizes h := h.elim
  snoc _ _ _ _ _ _ := by simp

theorem inv (h : PrefixBounds R k) : PrefixBounds (fun x y => R y x) k where
  sizes hxy := (h.sizes hxy).symm
  snoc x y hx hy a b := (h.snoc y x hy hx b a).trans (and_congr_left fun _ => eq_comm)

theorem union (h : PrefixBounds R k) (h' : PrefixBounds S l) :
    PrefixBounds (fun x y => R x y ∨ S x y) (max k l) := by
  let f := h.mono (Nat.le_max_left k l)
  let g := h'.mono (Nat.le_max_right k l)
  refine ⟨fun hh => hh.elim f.sizes g.sizes, ?_⟩
  intro x y hx hy a b
  rw [f.snoc x y hx hy, g.snoc x y hx hy, and_or_left]

theorem seq (h : PrefixBounds R k) (h' : PrefixBounds S l) :
    PrefixBounds (fun x y => ∃ z, R x z ∧ S z y) (k+l) := by
  constructor
  · rintro x y ⟨z,hr,hs⟩
    obtain ⟨h₁,h₂⟩ := h.sizes hr
    obtain ⟨h₃,h₄⟩ := h'.sizes hs
    constructor <;> omega
  · intro x y hx hy a b
    constructor
    · rintro ⟨z, hr, hs⟩
      obtain ⟨h₁,_⟩ := h.sizes hr
      obtain ⟨_,h₂⟩ := h'.sizes hs
      rcases List.eq_nil_or_concat z with rfl | ⟨z, c, rfl⟩
      · simp at h₁; omega
      · simp only [List.length_append, List.length_singleton, List.length_concat] at h₁ h₂
        rw [List.concat_eq_append] at hr hs
        obtain ⟨hac, hr'⟩ := (h.snoc x z (by omega) (by omega) a c).mp hr
        obtain ⟨hcb, hs'⟩ := (h'.snoc z y (by omega) (by omega) c b).mp hs
        exact ⟨hac.trans hcb, z, hr', hs'⟩
    · rintro ⟨rfl, z, hr, hs⟩
      obtain ⟨h₁,_⟩ := h.sizes hr
      obtain ⟨_,h₂⟩ := h'.sizes hs
      exact ⟨z ++ [a], (h.snoc x z (by omega) (by omega) a a).mpr ⟨rfl,hr⟩,
        (h'.snoc z y (by omega) (by omega) a a).mpr ⟨rfl,hs⟩⟩

/-- Equality of two entire graphs, including exclusion of extra accepting
outputs and equality of domains, is a bounded test on both word lengths. -/
theorem ext_iff (h : PrefixBounds R k) (g : PrefixBounds S k) :
    (∀ x y, R x y ↔ S x y) ↔
      ∀ x y, x.length ≤ 2*k → y.length ≤ 2*k → (R x y ↔ S x y) := by
  refine ⟨fun hh x y _ _ => hh x y, ?_⟩
  intro agree
  have small (x y : List A) (hs : x.length ≤ k ∨ y.length ≤ k) : R x y ↔ S x y := by
    constructor
    · intro hr
      obtain ⟨h₁,h₂⟩ := h.sizes hr
      exact (agree x y (by omega) (by omega)).mp hr
    · intro hr
      obtain ⟨h₁,h₂⟩ := g.sizes hr
      exact (agree x y (by omega) (by omega)).mpr hr
  intro x y
  induction x using (measure (fun w : List A => w.length)).wf.induction generalizing y with
  | h x ih =>
    by_cases hs : x.length ≤ k ∨ y.length ≤ k
    · exact small x y hs
    rcases List.eq_nil_or_concat x with rfl | ⟨x,a,rfl⟩
    · simp at hs
    rcases List.eq_nil_or_concat y with rfl | ⟨y,b,rfl⟩
    · simp at hs
    simp only [List.length_concat, not_or] at hs
    rw [List.concat_eq_append, List.concat_eq_append]
    rw [h.snoc _ _ (by omega) (by omega), g.snoc _ _ (by omega) (by omega),
      ih x (by change x.length < (x.concat a).length; simp) y]

end PrefixBounds

/-- One prefix rewrite. Both heads have fixed lengths and a common omitted
suffix. Setting terminal accepts the exact heads only. -/
structure RewriteBox (P A : Type*) where
  left : Nat
  right : Nat
  terminal : Bool
  accepts : P → List A → List A → Prop

namespace RewriteBox

variable {P A : Type*}

def Rel (r : RewriteBox P A) (p : P) (x y : List A) : Prop :=
  r.left ≤ x.length ∧ r.right ≤ y.length ∧
    (r.terminal = true → x.length = r.left) ∧
    x.drop r.left = y.drop r.right ∧ r.accepts p (x.take r.left) (y.take r.right)

theorem bounds (r : RewriteBox P A) (p : P) : PrefixBounds (r.Rel p) (max r.left r.right + 1) := by
  constructor
  · intro x y h
    have hl := h.1
    have hr := h.2.1
    have he := congrArg List.length h.2.2.2.1
    simp only [List.length_drop] at he
    constructor <;> omega
  · intro x y hx hy a b
    have hl : r.left ≤ x.length := by omega
    have hr : r.right ≤ y.length := by omega
    unfold Rel
    simp only [List.length_append, List.length_singleton,
      List.drop_append_of_le_length hl, List.drop_append_of_le_length hr,
      List.take_append_of_le_length hl, List.take_append_of_le_length hr,
      List.append_eq_append_iff_of_size_eq_right (by simp : [a].length = [b].length),
      List.cons.injEq, and_true]
    by_cases ht : r.terminal = true <;> simp [ht] <;> grind

end RewriteBox
end KnightModel.RankTwo
