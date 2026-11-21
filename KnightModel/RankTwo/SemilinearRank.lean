import KnightModel.RankTwo.SemilinearSelection
import KnightModel.RankTwo.RankFrame

/-! # Canonical parameters from semilinear transition fibers -/

namespace KnightModel.RankTwo.Semilinear

open UnaryChoice

variable {G I F V A K : Type*} [Group G] [MulAction G F] [Zero A]
    [MulAction G (I →₀ A)] [AddCommGroup V] [Module ℚ V] [LinearOrder V]
    [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] [DenselyOrdered V] [MulAction G V]

/-- Definability of the parameter fiber suffices to extract the finite supports
used for rank two. The ordered vector space may be a type synonym of the flat
coefficient functions, identified by an equivariant bijection. -/
theorem hasCanonicalParameters_of_semilinear_fibers
    {P : Samples V} (samples : AffineSamples P) (iso : G → V ≃o V)
    (action : ∀ g x, iso g x = g • x) (pres : ∀ g, Preserves (P := P) (iso g))
    (vec : V ≃ (I →₀ A)) (mapVec : ∀ (g : G) x, vec (g • x) = g • vec x)
    (r : F → F → Prop) (arity : K → ℕ)
    (R : (k : K) → F → F → (Fin (arity k) → I →₀ A) → Prop)
    (covers : ∀ u v, r u v → ∃ k p, R k u v p)
    (functional : ∀ k u u' v p, R k u v p → R k u' v p → u = u')
    (invariant : ∀ (g : G) k u v p,
      R k u v p ↔ R k (g • u) (g • v) (fun j => g • p j))
    (definable : ∀ k u v, Definable {p : Fin (arity k) → V | R k u v (fun i => vec (p i))}) :
    HasCanonicalParameters G I A r := by
  apply hasCanonicalParameters_of_transition_fibers arity R covers functional invariant
  rintro k u v ⟨w, hw⟩
  have hne : ({p : Fin (arity k) → V | R k u v (fun i => vec (p i))} : Set _).Nonempty :=
    ⟨fun i => vec.symm (w i), by simpa using hw⟩
  obtain ⟨p, hp, fixed⟩ := (definable k u v).exists_fixed samples iso action pres hne
  refine ⟨fun i => vec (p i), hp, ?_⟩
  intro g hg
  have hfixed := fixed g fun q => by
    change R k u v (fun i => vec (q i)) ↔ R k u v (fun i => vec (g • q i))
    simpa only [mapVec] using hg (fun i => vec (q i))
  intro i
  rw [← mapVec, hfixed i]

end KnightModel.RankTwo.Semilinear
