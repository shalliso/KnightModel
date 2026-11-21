import KnightModel.MainResults
import KnightModel.RankTwo.SquareAtlas

/-! # Existence of the square atlas from the Knight-model existence theorem -/

namespace KnightModel.RankTwo

open Cardinal Set

/-- Existence of the large ordered line and its cofinal family of actual
charts. Both the index order and the chart alphabet come from the construction. -/
theorem exists_square_atlas (hs : SquareAtOmegaOne) :
    ∃ (Ω I : Type) (_ : Blueprint Ω) (_ : KnightModel I Ω)
      (X : Type) (_ : LinearOrder X), #I = ℵ₁ ∧ #X = aleph 2 ∧
      ∃ a : OuterIndex ↪o X, (∀ x, ∃ b, x ≤ a b) ∧
        ∀ b, Nonempty (Iic (a b) ≃o Word (Letter I)) := by
  obtain ⟨Ω, ⟨hΩ⟩⟩ := exists_blueprint
  letI := hΩ
  obtain ⟨I, hK, hI⟩ := exists_aleph_one_model (Ω := Ω)
  letI := hK
  have hunc : ¬ Countable I := by
    intro hc
    exact aleph0_lt_aleph_one.not_ge (hI ▸ mk_le_aleph0_iff.mpr hc)
  haveI : Nonempty I := not_isEmpty_iff.mp (fun h => hunc (by letI := h; infer_instance))
  obtain ⟨S⟩ := hs
  obtain ⟨X, ordX, cardX, charts⟩ := squareAtlas_on (Ω := Ω) S hunc
  exact ⟨Ω, I, hΩ, hK, X, ordX, hI, cardX, charts⟩

end KnightModel.RankTwo
