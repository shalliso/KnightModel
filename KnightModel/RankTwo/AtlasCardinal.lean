import KnightModel.RankTwo.Atlas
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family

/-! # Size of the outer line of a marked atlas -/

namespace KnightModel.RankTwo

open Cardinal

namespace MarkedRows

variable {J W : Type} [LinearOrder J] [LinearOrder W] [OrderTop W]
variable (D : MarkedRows J W)

/-- The outer line has one marked point per index and at most one point per index-word pair. -/
theorem mk_outer (hJ : ℵ₀ ≤ #J) (hW : #W ≤ #J) : #D.Outer = #J := by
  apply le_antisymm
  · calc
      #D.Outer ≤ #(J ×ₗ W) := Cardinal.mk_le_of_injective Subtype.val_injective
      _ = #J * #W := Cardinal.mk_prod _ _
      _ ≤ #J * #J := mul_le_mul' le_rfl hW
      _ = #J := Cardinal.mul_eq_self hJ
  · exact Cardinal.mk_le_of_injective D.anchor_strictMono.injective

theorem mk_outer_aleph_two (hJ : #J = aleph 2) (hW : #W ≤ aleph 2) :
    #D.Outer = aleph 2 :=
  (D.mk_outer (by rw [hJ]; exact aleph0_le_aleph 2) (by rwa [hJ])).trans hJ

/-- Specialization to the indices below the second uncountable initial ordinal. -/
theorem mk_outer_omega_two (rows : MarkedRows (aleph 2).ord.ToType W)
    (hW : #W ≤ aleph 2) : #rows.Outer = aleph 2 := by
  apply rows.mk_outer_aleph_two _ hW
  rw [Cardinal.mk_toType, Cardinal.card_ord]

end MarkedRows
end KnightModel.RankTwo
