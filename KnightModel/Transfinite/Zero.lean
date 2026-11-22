import KnightModel.Transfinite.Seed
import KnightModel.Transfinite.Comparison
import KnightModel.RankTwo.RankModel

/-! # A rigid countably infinite starting seed -/

namespace KnightModel.Transfinite

open RankTwo.Scott Cardinal

noncomputable section

private abbrev ZeroCarrier := (ℵ₀ : Cardinal.{0}).ord.ToType

private instance : Countable ZeroCarrier :=
  Cardinal.mk_le_aleph0_iff.mp (Cardinal.mk_ord_toType _).le

/-- A binary order predicate and a separate unary name for every point. -/
private def ZeroRelation (n : ℕ) := (PLift (n = 2)) ⊕ (PLift (n = 1) × ZeroCarrier)

private instance (n : ℕ) : Countable (ZeroRelation n) := by unfold ZeroRelation; infer_instance

private def zeroModel : Model ZeroRelation ZeroCarrier
  | _, .inl ⟨rfl⟩, t => t 0 ≤ t 1
  | _, .inr (⟨rfl⟩, x), t => t 0 = x

/-- Every point in the starting structure is named. -/
def zeroSeed : Seed where
  R := ZeroRelation
  M := ZeroCarrier
  D := zeroModel
  countRel := inferInstance
  countM := inferInstance
  ord := inferInstance
  mark := Classical.ofNonempty
  leSym := .inl ⟨rfl⟩
  le_iff := fun _ => Iff.rfl
  markSym := .inr (⟨rfl⟩, Classical.ofNonempty)
  mark_iff := fun _ => Iff.rfl

theorem zeroSeed_tuple {n : ℕ} (x : Fin n → zeroSeed.M) :
    ComparisonLE (0 : Ordinal.{0}) (⊤ : Subgroup ↥(automorphismGroup zeroSeed.D)) x := by
  apply (comparisonLE_zero ..).2
  intro g _
  funext i
  exact (g.property (show ZeroRelation 1 from .inr (⟨rfl⟩, x i)) (fun _ => x i)).mp rfl

/-- The starting seed itself realizes the desired size and increasing order. -/
def zeroSeed_realizes : zeroSeed.Realizes ℵ₀ where
  N := ZeroCarrier
  E := zeroModel
  ord := inferInstance
  mark := zeroSeed.mark
  le_iff := zeroSeed.le_iff
  mark_iff := zeroSeed.mark_iff
  sat := zeroSeed.pres.satisfies_self zeroSeed.D
  seq := (OrderIso.refl _).toOrderEmbedding
  size := Cardinal.mk_ord_toType _

end
end KnightModel.Transfinite
