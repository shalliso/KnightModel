import KnightModel.RankTwo.AmalgamationCantor
import Mathlib.SetTheory.Cardinal.Continuum

/-! # A countable-or-continuum dichotomy for actual automorphism restrictions -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Set Cardinal

variable {R : ℕ → Type u} {M : Type} (D : Model R M) (B : List M) (P : Set M)

abbrev BaseAutomorphism := {g : ↥(automorphismGroup D) // Fixes g B}

variable (pres : ∀ g : ↥(automorphismGroup D), Fixes g B → ∀ x, x ∈ P ↔ g.val x ∈ P)

noncomputable def restrictToSet (g : BaseAutomorphism D B) : Equiv.Perm P :=
  g.val.val.subtypeEquiv (pres g.val g.property)

private theorem finite_motion_of_uncountable [Countable M]
    (unc : ¬ (range (restrictToSet D B P pres)).Countable) (s : Finset M) :
    ∃ g : ↥(automorphismGroup D), Fixes g B ∧ (∀ x ∈ s, g.val x = x) ∧
      ∃ p ∈ P, g.val p ≠ p := by
  classical
  by_contra h
  apply unc
  let I := range (restrictToSet D B P pres)
  let rep (x : I) := x.property.choose
  let code (x : I) (z : s) := (rep x).val.val z.val
  have inj : Function.Injective code := by
    intro x y e
    let g := rep x
    let f := rep y
    let t := f.val⁻¹ * g.val
    have base : Fixes t B := by
      intro b hb
      change f.val.val.symm (g.val.val b) = b
      exact (congrArg f.val.val.symm ((g.property b hb).trans (f.property b hb).symm)).trans
        (f.val.val.symm_apply_apply b)
    have control (z) (hz : z ∈ s) : t.val z = z := by
      change f.val.val.symm (g.val.val z) = z
      rw [show g.val.val z = f.val.val z from congrFun e ⟨z,hz⟩, f.val.val.symm_apply_apply]
    have point (p : P) : g.val.val p.val = f.val.val p.val := by
      have ht : t.val p.val = p.val := by
        by_contra ne
        exact h ⟨t,base,control,p.val,p.property,ne⟩
      exact f.val.val.symm_apply_eq.mp ht
    apply Subtype.ext
    rw [← x.property.choose_spec, ← y.property.choose_spec]
    exact Equiv.ext fun p => Subtype.ext (point p)
  exact inj.countable

/-- For a countable relational structure the image of the finite-base
stabilizer on an invariant subset is countable or has size continuum. -/
theorem countable_or_continuum_restrictions (enum : ℕ → M) (onto : Function.Surjective enum) :
    (range (restrictToSet D B P pres)).Countable ∨ #(range (restrictToSet D B P pres)) = 2 ^ ℵ₀ := by
  classical
  by_cases h : (range (restrictToSet D B P pres)).Countable
  · exact Or.inl h
  apply Or.inr
  haveI : Countable M := onto.countable
  obtain ⟨e,he⟩ := cantor_restrictions_of_finite_motion D B P enum onto
    (finite_motion_of_uncountable D B P pres h) pres
  have realized (b : ℕ → Bool) : e b ∈ range (restrictToSet D B P pres) := by
    obtain ⟨g,hg,hp⟩ := he b
    exact ⟨⟨g,hg⟩,Equiv.ext (fun p => Subtype.ext (hp p).symm)⟩
  let embed (b : ℕ → Bool) : range (restrictToSet D B P pres) := ⟨e b,realized b⟩
  have inj : Function.Injective embed := fun _ _ heq => e.injective (congrArg Subtype.val heq)
  apply le_antisymm
  · calc
      #(range (restrictToSet D B P pres)) ≤ #(Equiv.Perm P) := mk_set_le _
      _ ≤ #(P → P) := mk_le_of_injective (f := fun g : Equiv.Perm P => g.toFun)
        (fun _ _ h => Equiv.ext (congrFun h))
      _ = #P ^ #P := by simp only [mk_arrow, lift_id]
      _ ≤ ℵ₀ ^ ℵ₀ := (power_le_power_right mk_le_aleph0).trans (power_le_power_left aleph0_ne_zero mk_le_aleph0)
      _ = 2 ^ ℵ₀ := aleph0_power_aleph0.trans two_power_aleph0.symm
  · simpa [mk_arrow] using mk_le_of_injective inj

end KnightModel.RankTwo.Scott.MarkedExtension
