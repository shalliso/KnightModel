import KnightModel.RankTwo.Rank
import Mathlib.Algebra.Group.Action.Basic

namespace KnightModel.RankTwo

variable {G X : Type*} [Group G] [MulAction G X]

private theorem fixes_conjugate {B : List X} (g h : G)
    (hh : Fixes h (B.map (g • ·))) : Fixes (g⁻¹ * h * g) B := by
  intro x hx
  have h' := hh (g • x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  simpa only [mul_smul, inv_smul_smul] using congrArg (fun y => g⁻¹ • y) h'

private theorem conjugate_unmap {B : List X} (g : G) {a b : X}
    (h : Conjugate G (B.map (g • ·)) (g • a) b) : Conjugate G B a (g⁻¹ • b) := by
  obtain ⟨f, hf, ha⟩ := h
  exact ⟨g⁻¹ * f * g, fixes_conjugate g f hf, by simp only [mul_smul, ha]⟩

/-- Moving both the point and its finite parameter list by an automorphism
preserves every finite stage of disjointifying rank. -/
theorem RankLE.smul {n : ℕ} {B : List X} {x : X}
    (h : RankLE G n B x) (g : G) : RankLE G n (B.map (g • ·)) (g • x) := by
  induction n generalizing B x with
  | zero =>
    intro f hf
    have hx := h (g⁻¹ * f * g) (fixes_conjugate g f hf)
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun y => g • y) hx
  | succ n ih =>
    rcases h with ⟨c, hc⟩ | hc
    · exact Or.inl ⟨g • c, fun c' h' => by
        simpa only [List.map_cons, smul_inv_smul] using ih (hc _ (conjugate_unmap g h'))⟩
    · apply Or.inr
      intro y hy
      rcases hc _ (conjugate_unmap g hy) with h | h
      · exact Or.inl (by simpa only [List.map_cons, smul_inv_smul] using ih h)
      · exact Or.inr (by simpa only [List.map_cons, smul_inv_smul] using ih h)

end KnightModel.RankTwo
