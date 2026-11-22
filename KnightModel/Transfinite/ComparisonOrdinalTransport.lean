import KnightModel.RankTwo.RankOrdinal
import Mathlib.Algebra.Group.Action.Basic

/-! # Transport of the original ordinal rank

The smaller ordinal may vary with the point in the witness orbit. Translating
the whole parameter set first allows the witness to be held fixed when the
ranked point is moved.
-/

namespace KnightModel.RankTwo

universe w

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

private theorem fixes_conj_of_image (g k : G) (B : Finset X)
    (hk : ∀ b ∈ B.image (g • ·), k • b = b) :
    ∀ b ∈ B, (g⁻¹ * k * g) • b = b := by
  intro b hb
  simp only [mul_smul, hk _ (Finset.mem_image_of_mem _ hb), inv_smul_smul]

private theorem conjugate_pull (g : G) {B : Finset X} {x y : X}
    (h : ConjugateOverSet G (B.image (g • ·)) (g • x) y) :
    ConjugateOverSet G B x (g⁻¹ • y) := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨g⁻¹ * k * g, fixes_conj_of_image g k B hk, by simp only [mul_smul]⟩

/-- Original ordinal disjointifying rank is invariant under a simultaneous
translation of the point and finite base. -/
theorem OrdinalRankLE.smul {α : Ordinal.{w}} {B : Finset X} {x : X}
    (rank : OrdinalRankLE G α B x) (g : G) :
    OrdinalRankLE G α (B.image (g • ·)) (g • x) := by
  induction α using WellFoundedLT.induction generalizing B x with
  | ind α ih =>
    rw [OrdinalRankLE] at rank ⊢
    by_cases hα : α = 0
    · rw [if_pos hα] at rank ⊢
      intro k hk
      have hx := rank (g⁻¹ * k * g) (fixes_conj_of_image g k B hk)
      simpa only [mul_smul, smul_inv_smul] using congrArg (g • ·) hx
    rw [if_neg hα] at rank ⊢
    rcases rank with ⟨c, hc⟩ | hc
    · refine Or.inl ⟨g • c, ?_⟩
      intro d hd
      obtain ⟨β, hβ, hr⟩ := hc _ (conjugate_pull g hd)
      exact ⟨β, hβ, by simpa using ih β hβ hr⟩
    · apply Or.inr
      intro y hy
      rcases hc _ (conjugate_pull g hy) with ⟨β, hβ, hr⟩ | ⟨β, hβ, hr⟩
      · exact Or.inl ⟨β, hβ, by simpa using ih β hβ hr⟩
      · exact Or.inr ⟨β, hβ, by simpa using ih β hβ hr⟩

/-- Hold the witness fixed while varying the conjugate realization of the
point, preserving the existence of a rank strictly below the given stage. -/
theorem ordinal_transport_witness {α : Ordinal.{w}} {B : Finset X} {x z c : X}
    (g : G) (hg : ∀ b ∈ B, g • b = b) (hz : g • x = z)
    (hw : ∀ c', ConjugateOverSet G B c c' →
      ∃ β, ∃ _ : β < α, OrdinalRankLE G β (insert c' B) x) :
    ∃ β, ∃ _ : β < α, OrdinalRankLE G β (insert c B) z := by
  have hi (b : X) (hb : b ∈ B) : g⁻¹ • b = b := by
    simpa only [inv_smul_smul] using (congrArg (g⁻¹ • ·) (hg b hb)).symm
  have he : B.image (g • ·) = B := by
    calc
      B.image (g • ·) = B.image id := Finset.image_congr hg
      _ = B := Finset.image_id ..
  obtain ⟨β, hβ, hr⟩ := hw (g⁻¹ • c) ⟨g⁻¹, hi, rfl⟩
  exact ⟨β, hβ, by simpa [hz, he] using hr.smul g⟩

end KnightModel.RankTwo
