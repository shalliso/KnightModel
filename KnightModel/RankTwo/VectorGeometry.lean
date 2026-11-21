import KnightModel.RankTwo.Alphabet
import KnightModel.RankTwo.UnaryChoice
import Mathlib.Algebra.Order.Module.Rat
import Mathlib.Data.Finsupp.SMul

/-! # Midpoints and invariant interval samples in the Knight vector group -/

namespace KnightModel.RankTwo

variable {I : Type} [LinearOrder I]

noncomputable instance vectorModule : Module ℚ (VectorGroup I) :=
  inferInstanceAs (Module ℚ (I →₀ ℚ))

instance vectorPosSMulStrictMono : PosSMulStrictMono ℚ (VectorGroup I) where
  smul_lt_smul_of_pos_left q hq x y h := by
    obtain ⟨i, hi, hlt⟩ := Finsupp.Colex.lt_iff.mp h
    refine Finsupp.Colex.lt_iff.mpr ⟨i, ?_, ?_⟩
    · intro j hij
      change q * x j = q * y j
      rw [hi j hij]
    · change q * x i < q * y i
      exact mul_lt_mul_of_pos_left hlt hq

theorem midpoint_between {a b : VectorGroup I} (h : a < b) :
    a < (2 : ℚ)⁻¹ • (a + b) ∧ (2 : ℚ)⁻¹ • (a + b) < b := by
  have hp : (0 : ℚ) < 2 := by decide
  rw [lt_inv_smul_iff_of_pos hp, inv_smul_lt_iff_of_pos hp, two_smul, two_smul]
  exact ⟨add_lt_add_right h _, add_lt_add_left h _⟩

instance vectorDenselyOrdered : DenselyOrdered (VectorGroup I) where
  dense _ _ h := ⟨_, midpoint_between h⟩

/-- The distinguished basis vector supplies the shifts needed for unbounded
intervals. Rational division by two supplies the interior point of bounded ones. -/
noncomputable def vectorSamples (d : VectorGroup I) (hd : 0 < d) :
    UnaryChoice.Samples (VectorGroup I) where
  base := 0
  down x := x - d
  up x := x + d
  mid x y := (2 : ℚ)⁻¹ • (x + y)
  down_lt _ := sub_lt_self _ hd
  lt_up _ := lt_add_of_pos_right _ hd
  between _ _ := midpoint_between

/-- Every ordered linear symmetry fixing d preserves the sample operations. -/
theorem preserves_vectorSamples {d : VectorGroup I} (hd : 0 < d)
    (e : VectorGroup I ≃o VectorGroup I)
    (f : VectorGroup I →ₗ[ℚ] VectorGroup I)
    (hf : ∀ x, e x = f x) (fixD : e d = d) :
    UnaryChoice.Preserves (P := vectorSamples d hd) e where
  base := by simpa only [vectorSamples, hf] using f.map_zero
  down x := by
    change e (x - d) = e x - d
    rw [hf, map_sub, ← hf x, ← hf d, fixD]
  up x := by
    change e (x + d) = e x + d
    rw [hf, map_add, ← hf x, ← hf d, fixD]
  mid x y := by
    change e ((2 : ℚ)⁻¹ • (x + y)) = (2 : ℚ)⁻¹ • (e x + e y)
    simp only [hf, map_smul, map_add]

end KnightModel.RankTwo
