import KnightModel.RankTwo.Amalgamation
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Group.Basic

/-! # The Baire-category step for the relative automorphism group -/

namespace KnightModel.RankTwo.Amalgamation

open Set

variable {G M P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [BaireSpace G]

/-- If all point evaluations of the restriction homomorphism have closed fibers,
its pointwise kernel has interior as soon as the image is countable. -/
theorem open_neighborhood_in_kernel (r : G →* Equiv.Perm P)
    (closed : ∀ p q : P, IsClosed {g : G | r g p = q})
    (count : (range r).Countable) :
    ∃ U : Set G, IsOpen U ∧ 1 ∈ U ∧ ∀ g ∈ U, r g = 1 := by
  classical
  letI : Countable (range r) := count
  let fiber (t : range r) := {g : G | r g = t.val}
  have hc (t : range r) : IsClosed (fiber t) := by
    have he : fiber t = ⋂ p : P, {g : G | r g p = t.val p} := by
      ext g
      exact ⟨fun h => mem_iInter.mpr fun p => congrArg (fun σ : Equiv.Perm P => σ p) h, fun h => Equiv.ext fun p => mem_iInter.mp h p⟩
    rw [he]
    exact isClosed_iInter (fun p => closed p (t.val p))
  have cover : (⋃ t, fiber t) = univ := eq_univ_of_forall fun g =>
    mem_iUnion.mpr ⟨⟨r g,⟨g,rfl⟩⟩,rfl⟩
  obtain ⟨t,a,ha⟩ := nonempty_interior_of_iUnion_of_closed hc cover
  let U := (fun g : G => a*g) ⁻¹' interior (fiber t)
  refine ⟨U,isOpen_interior.preimage (continuous_const_mul a),?_,?_⟩
  · change a*1 ∈ interior (fiber t)
    simpa only [mul_one] using ha
  · intro g hg
    have h₁ : r a = t.val := (show a ∈ fiber t from interior_subset ha)
    have h₂ : r (a*g) = t.val := (show a*g ∈ fiber t from interior_subset hg)
    rw [map_mul,← h₁] at h₂
    exact mul_left_cancel (h₂.trans (mul_one (r a)).symm)

/-- Applied to the pointwise-convergence topology, a countable permutation image
would be fixed pointwise by the stabilizer of some finite set of old elements. -/
theorem uncountable_restrictions_of_finite_motion [MulAction G M] (r : G →* Equiv.Perm P)
    (closed : ∀ p q : P, IsClosed {g : G | r g p = q})
    (basis : ∀ U : Set G, IsOpen U → 1 ∈ U → ∃ F : Finset M,
      ∀ g : G, (∀ x ∈ F, g • x = x) → g ∈ U)
    (moves : ∀ F : Finset M, ∃ g : G, (∀ x ∈ F, g • x = x) ∧ r g ≠ 1) :
    ¬ (range r).Countable := by
  intro hc
  obtain ⟨U,hu,h₁,hk⟩ := open_neighborhood_in_kernel r closed hc
  obtain ⟨F,hF⟩ := basis U hu h₁
  obtain ⟨g,hg,hn⟩ := moves F
  exact hn (hk g (hF g hg))

end KnightModel.RankTwo.Amalgamation
