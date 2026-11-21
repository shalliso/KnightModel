import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Stabilizer-fixed selection in finite powers

The code fiber for a frame transition is a nonempty definable set of parameter
tuples. A point fixed by its setwise stabilizer can be obtained one coordinate
at a time. The proof uses only unary selection, closure under projection, and
closure under parameter fibers, so it applies in particular to semilinear sets.
-/

namespace KnightModel.RankTwo

variable {G V : Type*} [Group G] [MulAction G V]

/-- First-coordinate projection of a set of nonempty tuples. -/
def headProjection {n : ℕ} (S : Set (Fin (n + 1) → V)) : Set V :=
  {z | ∃ t : Fin n → V, Fin.cons z t ∈ S}

/-- The remaining coordinates of the tuples with first coordinate `z`. -/
def tailFiber {n : ℕ} (S : Set (Fin (n + 1) → V)) (z : V) : Set (Fin n → V) :=
  {t | Fin.cons z t ∈ S}

private theorem map_cons {n : ℕ} (g : G) (z : V) (t : Fin n → V) :
    (fun j => g • (Fin.cons z t j)) = Fin.cons (g • z) (fun j => g • t j) := by
  funext j
  exact Fin.cases (by simp) (fun i => by simp) j

private theorem preserves_headProjection {n : ℕ} (S : Set (Fin (n + 1) → V)) (g : G)
    (hg : ∀ p, p ∈ S ↔ (fun j => g • p j) ∈ S) (z : V) :
    z ∈ headProjection S ↔ g • z ∈ headProjection S := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, map_cons g z t ▸ (hg _).mp ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun j => g⁻¹ • t j, (hg _).mpr ?_⟩
    simpa only [map_cons, smul_inv_smul] using ht

/-- Finite-tuple selection from unary selection. Both stabilizers in the
statement act by the original group, without enlarging the group to all
permutations of an individual fiber. -/
theorem tuple_stabilizer_fixed_selection
    (unary : Set V → Prop) (family : ∀ n : ℕ, Set (Fin n → V) → Prop)
    (projection : ∀ n S, family (n + 1) S → unary (headProjection S))
    (fiber : ∀ n S z, family (n + 1) S → family n (tailFiber S z))
    (chooseUnary : ∀ S, unary S → S.Nonempty →
      ∃ z ∈ S, ∀ g : G, (∀ w, w ∈ S ↔ g • w ∈ S) → g • z = z) :
    ∀ n S, family n S → S.Nonempty →
      ∃ p ∈ S, ∀ g : G, (∀ q, q ∈ S ↔ (fun j => g • q j) ∈ S) →
        ∀ j, g • p j = p j := by
  intro n
  induction n with
  | zero =>
    intro S _ hne
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, fun _ _ j => Fin.elim0 j⟩
  | succ n ih =>
    intro S hS hne
    obtain ⟨q, hq⟩ := hne
    have head_nonempty : (headProjection S).Nonempty :=
      ⟨q 0, Fin.tail q, by simpa only [Fin.cons_self_tail] using hq⟩
    obtain ⟨z, hz, fixedZ⟩ := chooseUnary _ (projection n S hS) head_nonempty
    obtain ⟨t, ht, fixedT⟩ := ih _ (fiber n S z hS) hz
    refine ⟨Fin.cons z t, ht, ?_⟩
    intro g hg
    have gz : g • z = z := fixedZ g (preserves_headProjection S g hg)
    have gt := fixedT g fun q => by
      change Fin.cons z q ∈ S ↔ Fin.cons z (fun j => g • q j) ∈ S
      simpa only [map_cons, gz] using hg (Fin.cons z q)
    intro j
    exact Fin.cases (by simpa only [Fin.cons_zero] using gz)
      (fun i => by simpa only [Fin.cons_succ] using gt i) j

end KnightModel.RankTwo
