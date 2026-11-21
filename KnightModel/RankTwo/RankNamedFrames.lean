import KnightModel.RankTwo.FrameAutomorphisms
import KnightModel.RankTwo.RankFrameRelations
import KnightModel.RankTwo.SemilinearRank
import KnightModel.RankTwo.VectorSampling
import Mathlib.Logic.Equiv.Sum

/-! # Singleton rank in the named frame interpretation -/

namespace KnightModel.RankTwo.Scott

open Semilinear

variable {Ω I C F : Type} [Blueprint Ω] [KnightModel I Ω] {K : Nat → Type}
    {A : FrameAction C F} (i₀ : I) (T : FrameInterpretation (BaseRelation Ω) K (BasePoints I) A)
    (base_eq : ∀ {n} (r : BaseRelation Ω n) t, T.base r t ↔ baseModel i₀ r t)

local notation "G" => (automorphismGroup T.model : Type _)
local notation "V" => VectorGroup I
local notation "ix" => indexSort i₀ T base_eq
local notation "vx" => vectorSort i₀ T base_eq
local notation "fx" => frameSort T

/-- Over a fixed upper frame a given target frame accepts at most one code.
Thus the transition fiber is empty, or is exactly the fiber naming one code. -/
theorem FrameInterpretation.transition_definable
    (definable : ∀ {n} (k : K n) (c : C), Definable {p : Fin n → V |
      T.run k (Sum.inr ∘ p) = some c})
    {n} (k : K n) (u v : F) : Definable {p : Fin n → V | T.Transition k u v (Sum.inr ∘ p)} := by
  by_cases h : A.Below u v
  · obtain ⟨c, hc⟩ := h
    obtain ⟨φ, hφ⟩ := definable k c
    refine ⟨φ, fun p => Iff.trans ?_ (hφ p)⟩
    constructor
    · rintro ⟨b, hb, hu⟩
      exact T.faithful v b c (hu.trans hc.symm) ▸ hb
    · exact fun hr => ⟨c, hr, hc⟩
  · exact ⟨.ltZero (.const 0), fun p => iff_of_false (fun ⟨c, _, hc⟩ => h ⟨c, hc⟩) (lt_irrefl _)⟩

/-- Naming the base structure and the transition programs forces singleton
rank at most two in the full relational model. Only coverage of codes and
semilinearity of their program parameter fibers enter from program semantics. -/
theorem namedFrame_rankLE_two_of_samples
    (iso : G → V ≃o V) (iso_map : ∀ g x, iso g x = (vx).map g x)
    (sample_pres : ∀ g, UnaryChoice.Preserves
      (P := vectorSamples (unitLetter i₀).val (unitLetter_pos i₀)) (iso g))
    (covers : ∀ c : C, ∃ (n : ℕ) (k : K n) (p : Fin n → V), T.run k (Sum.inr ∘ p) = some c)
    (definable : ∀ {n} (k : K n) (c : C), Definable {p : Fin n → V |
      T.run k (Sum.inr ∘ p) = some c}) (x : BasePoints I ⊕ F) :
    ModelRankLE T.model 2 [] x := by
  letI : MulAction G I := (ix).action
  letI : MulAction G V := (vx).action
  letI : MulAction G (I →₀ ℚ) := (vx).action
  letI : MulAction G F := (fx).action
  let e : (I ⊕ ((I →₀ ℚ) ⊕ F)) ≃ (BasePoints I ⊕ F) := (Equiv.sumAssoc I V F).symm
  have equiv (g : G) (y : I ⊕ ((I →₀ ℚ) ⊕ F)) : e (g • y) = g.val (e y) := by
    cases y with
    | inl z => exact (ix).incl_map g z
    | inr z => cases z with
      | inl v => exact (vx).incl_map g v
      | inr f => exact (fx).incl_map g f
  let rel (k : Σ n, K n) (u v : F) (p : Fin k.1 → I →₀ ℚ) :=
    T.Transition k.2 u v (Sum.inr ∘ p)
  have params : HasCanonicalParameters G I ℚ A.Below := by
    apply hasCanonicalParameters_of_semilinear_fibers (vectorAffineSamples i₀) iso iso_map sample_pres
      (show V ≃ (I →₀ ℚ) from Equiv.refl _) (fun _ _ => rfl) A.Below
      (fun k : Σ n, K n => k.1) rel
    · rintro u v ⟨c, hc⟩
      obtain ⟨n, k, p, hp⟩ := covers c
      exact ⟨⟨n, k⟩, p, c, hp, hc⟩
    · exact fun k _ _ v p => T.transition_functional k.2 v (Sum.inr ∘ p)
    · exact fun g k u v p => T.invariant_transition Sum.inr g ((fx).map g) ((vx).map g)
        ((fx).incl_map g) ((vx).incl_map g) k.2 u v p
    · exact fun k u v => T.transition_definable definable k.2 u v
  exact threeSort_modelRankLE_two T.model e equiv (fixesBelow_of_knight (index_commutes i₀ T base_eq))
    (index_monotone i₀ T base_eq) (coefficient_map i₀ T base_eq) A.Below A.below_total
    (fun g {u v} => (T.invariant_below g ((fx).map g) ((fx).incl_map g) u v).mp) params x

end KnightModel.RankTwo.Scott
