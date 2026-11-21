import KnightModel.RankTwo.MarkedExtensionGrowth
import KnightModel.RankTwo.MarkedExtensionLift

/-! # The countable marked-extension criterion for an ℵ₂-sized Scott model -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal

/-- A nonempty isomorphism-invariant family of countable marked extensions,
closed under countable increasing unions and admitting lifts of countable
elementary base changes, suffices to realize the Scott sentence at ℵ₂. -/
theorem aleph_two_of_marked_family {R : ℕ → Type} {M : Type} (C : Presentation R M)
    (D : Model R M) (F : Family (C.sentence D)) :
    ∃ (N : Type) (E : Model R N), #N = aleph 2 ∧ BackAndForth.Satisfies E (C.sentence D) := by
  haveI : Countable M := Function.Surjective.countable (f := C.enum) C.onto
  let A : World R := ⟨M, D⟩
  obtain ⟨V, size, sat⟩ := exists_aleph_two_of_small_extensions (C.sentence D) A
    (C.satisfies_self D) ((mk_le_aleph0 (α := M)).trans (aleph0_le_aleph 1)) (C.enum 0) (by
      intro B hB sizeB
      obtain ⟨p, hp⟩ := Family.extend C D F B hB sizeB
      exact ⟨p.target, p.embed, p.mark, hp, p.fresh⟩)
  exact ⟨V.carrier, V.model, size, sat⟩

end KnightModel.RankTwo.Scott.MarkedExtension
