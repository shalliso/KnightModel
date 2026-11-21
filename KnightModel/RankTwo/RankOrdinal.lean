import KnightModel.RankTwo.Rank
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! # The finite ranks are exactly the finite stages of Allison's ordinal recursion

Section 4.2 of Allison's paper uses finite sets of parameters, pointwise
stabilizers and a separately quantified ordinal below each positive stage.
Here that definition is stated literally, with the fixing witness and conjugate
points in the original carrier. Its restriction to natural ordinals agrees
with the cumulative finite-stage predicate used by the frame construction.
-/

namespace KnightModel.RankTwo

universe w

variable {G X : Type*} [Group G] [MulAction G X]

/-- Conjugacy over a finite set, using its pointwise stabilizer. -/
def ConjugateOverSet (G : Type*) [Group G] [MulAction G X] (B : Finset X) (a b : X) : Prop :=
  ∃ g : G, (∀ p ∈ B, g • p = p) ∧ g • a = b

variable [DecidableEq X]

/-- The ordinal-bound predicate for disjointifying rank from Allison §4.2.
The ordinal sought below the current bound can depend on the conjugate. -/
noncomputable def OrdinalRankLE (G : Type*) [Group G] [MulAction G X]
    (α : Ordinal.{w}) (B : Finset X) (a : X) : Prop :=
  if α = 0 then ∀ g : G, (∀ p ∈ B, g • p = p) → g • a = a
  else (∃ c : X, ∀ c', ConjugateOverSet G B c c' →
          ∃ β : Ordinal.{w}, ∃ _ : β < α, OrdinalRankLE G β (insert c' B) a) ∨
       (∀ a', ConjugateOverSet G B a a' →
          (∃ β : Ordinal.{w}, ∃ _ : β < α, OrdinalRankLE G β (insert a' B) a) ∨
          (∃ β : Ordinal.{w}, ∃ _ : β < α, OrdinalRankLE G β (insert a B) a'))
termination_by α

private theorem conjugate_set_iff (B : List X) (a b : X) :
    ConjugateOverSet G B.toFinset a b ↔ Conjugate G B a b := by
  simp only [ConjugateOverSet, Conjugate, Fixes, List.mem_toFinset]

omit [DecidableEq X] in
private theorem finite_bound_mono {i j : ℕ} {B : List X} {a : X}
    (h : i ≤ j) (rank : RankLE G i B a) : RankLE G j B a := by
  induction h with
  | refl => exact rank
  | step _ ih => exact ih.succ

/-- At every natural ordinal, the original finite-set recursion agrees with
the finite-list formulation of the singleton bound, including at rank two. -/
theorem ordinalRankLE_natCast_iff (n : ℕ) (B : List X) (a : X) :
    OrdinalRankLE G (n : Ordinal.{w}) B.toFinset a ↔ RankLE G n B a := by
  induction n using Nat.strong_induction_on generalizing B a with
  | h n ih =>
    cases n with
    | zero =>
      rw [OrdinalRankLE]
      simp only [Nat.cast_zero, ↓reduceIte, List.mem_toFinset]
      rfl
    | succ n =>
      have strict (L : List X) (z : X) :
          (∃ β : Ordinal.{w}, ∃ _ : β < (n.succ : Ordinal.{w}), OrdinalRankLE G β L.toFinset z) ↔
          RankLE G n L z := by
        constructor
        · rintro ⟨β, hb, rank⟩
          obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp (hb.trans (Ordinal.natCast_lt_omega0 n.succ))
          have hk : k < n.succ := Nat.cast_lt.mp hb
          exact finite_bound_mono (Nat.le_of_lt_succ hk) ((ih k hk L z).mp rank)
        · intro rank
          exact ⟨(n : Ordinal), Nat.cast_lt.mpr (Nat.lt_succ_self n),
            (ih n (Nat.lt_succ_self n) L z).mpr rank⟩
      have hn : (n.succ : Ordinal.{w}) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [OrdinalRankLE, if_neg hn]
      change _ ↔
        (∃ c, ∀ c', Conjugate G B c c' → RankLE G n (c' :: B) a) ∨
        (∀ b, Conjugate G B a b → RankLE G n (b :: B) a ∨ RankLE G n (a :: B) b)
      simp only [conjugate_set_iff, ← List.toFinset_cons, strict]

/-- The empty-base specialization used in the spectrum theorem. -/
theorem ordinalRankLE_empty_iff (n : ℕ) (a : X) :
    OrdinalRankLE G (n : Ordinal.{w}) ∅ a ↔ RankLE G n [] a := by
  simpa only [List.toFinset_nil] using ordinalRankLE_natCast_iff (G := G) n [] a

end KnightModel.RankTwo
