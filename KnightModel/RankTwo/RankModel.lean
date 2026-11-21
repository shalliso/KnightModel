import KnightModel.RankTwo.RankFrame
import KnightModel.RankTwo.ScottIso
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs

/-! # Disjointifying rank for the full automorphism group of a relational model -/

namespace KnightModel.RankTwo.Scott

universe u v

variable {R : ℕ → Type u} {M : Type v}

/-- All permutations preserving and reflecting each relation on every tuple. -/
def automorphismGroup (D : Model R M) : Subgroup (Equiv.Perm M) where
  carrier := {p | ∀ {k} (r : R k) (t : Tuple M k), D r t ↔ D r (p ∘ t)}
  one_mem' := fun {_} _ _ => Iff.rfl
  mul_mem' {p q} hp hq := fun {_} r t => (hq r t).trans (hp r (q ∘ t))
  inv_mem' {p} hp := by
    intro k r t
    change D r t ↔ D r (p.symm ∘ t)
    have h := (hp r (p.symm ∘ t)).symm
    have he : (p ∘ (p.symm ∘ t)) = t := funext fun i => p.apply_symm_apply (t i)
    rwa [he] at h

/-- The group consists exactly of the self-isomorphisms used by the Scott-sentence theorem. -/
def automorphismEquivRelIso (D : Model R M) : ↥(automorphismGroup D) ≃ RelIso D D where
  toFun p := ⟨p.val, p.val.symm, p.val.left_inv, p.val.right_inv, fun {_} r t => p.property r t⟩
  invFun f := ⟨⟨f.toFun, f.invFun, f.leftInv, f.rightInv⟩, by intro k r t; exact f.map_rel r t⟩
  left_inv p := by
    apply Subtype.ext
    exact Equiv.ext fun _ => rfl
  right_inv f := by cases f; rfl

/-- The natural action of the full automorphism group on the carrier of the model. -/
instance modelAutAction (D : Model R M) : MulAction ↥(automorphismGroup D) M where
  smul p x := p.val x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Finite disjointifying-rank bounds for the actual automorphisms of `D`. -/
abbrev ModelRankLE (D : Model R M) (n : ℕ) (B : List M) (x : M) : Prop :=
  RankLE ↥(automorphismGroup D) n B x

/-- A sort representation equivariant for the full model group computes rank bounds
in the ambient structure. No homogeneity or extension of partial automorphisms is assumed. -/
theorem modelRankLE_of_equivariant_embedding (D : Model R M)
    {X : Type*} [MulAction ↥(automorphismGroup D) X] (ι : X → M) (inj : Function.Injective ι)
    (equiv : ∀ (g : ↥(automorphismGroup D)) (x : X), ι (g • x) = g.val (ι x))
    {n : ℕ} {B : List X} {x : X} (h : RankLE ↥(automorphismGroup D) n B x) :
    ModelRankLE D n (B.map ι) (ι x) :=
  rankLE_of_equivariant_embedding ι inj equiv h

/-- In a relational structure presented by the three sorts, the finite-support
argument bounds the rank for its full automorphism group. -/
theorem threeSort_modelRankLE_two (D : Model R M) {I A F : Type*}
    [LinearOrder I] [Zero A] [MulAction ↥(automorphismGroup D) I]
    [MulAction ↥(automorphismGroup D) (I →₀ A)] [MulAction ↥(automorphismGroup D) F]
    (threeSorts : (I ⊕ ((I →₀ A) ⊕ F)) ≃ M)
    (equiv : ∀ (g : ↥(automorphismGroup D)) x, threeSorts (g • x) = g.val (threeSorts x))
    (below : FixesBelow ↥(automorphismGroup D) I)
    (mono : ∀ g : ↥(automorphismGroup D), Monotone (fun i : I => g • i))
    (coeff : ∀ (g : ↥(automorphismGroup D)) (v : I →₀ A) i, (g • v) (g • i) = v i)
    (r : F → F → Prop) (total : ∀ u v, r u v ∨ r v u)
    (pres : ∀ (g : ↥(automorphismGroup D)) {u v : F}, r u v → r (g • u) (g • v))
    (params : HasCanonicalParameters ↥(automorphismGroup D) I A r) (x : M) :
    ModelRankLE D 2 [] x := by
  obtain ⟨y, rfl⟩ := threeSorts.surjective x
  exact modelRankLE_of_equivariant_embedding D threeSorts threeSorts.injective equiv
    (threeSort_rankLE_two below mono coeff total pres params y)

end KnightModel.RankTwo.Scott
