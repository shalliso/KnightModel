import KnightModel.RankTwo.AtlasFrames
import KnightModel.RankTwo.AtlasCardinal

/-! # Cardinality of the actual frame sort

The same underlying frame may have many chart presentations. A surjection
bounds the number of distinct maps above, while their endpoints distinguish
the identity frames of the indexed charts.
-/
namespace KnightModel.RankTwo.MarkedRows

open Cardinal

variable {J W : Type} [LinearOrder J] [WellFoundedLT J] [LinearOrder W] [OrderTop W]
    (D : MarkedRows J W) (q : D.Transports) (C : CoordinateFamily W)

/-- Counting equivalence classes of presentations by their actual maps. -/
theorem cardinal_frames (hJ : ℵ₀ ≤ #J) (hC : #C.Code ≤ #J) :
    #(D.Frames q C) = #J := by
  apply le_antisymm
  · calc #(D.Frames q C) ≤ #(J × C.Code) := mk_le_of_surjective (D.present_surjective q C)
         _ = #J * #C.Code := by simp [mk_prod]
         _ ≤ #J * #J := mul_le_mul' le_rfl hC
         _ = #J := mul_eq_self hJ
  · exact mk_le_of_injective (D.frameAnchor_injective q C)

/-- Over ω₂, even after identifying all presentations of the same function,
the frame sort has size exactly ℵ₂. -/
theorem cardinal_frames_omega_two (D : MarkedRows (aleph.{0} 2).ord.ToType W)
    (q : D.Transports) (hC : #C.Code ≤ aleph 2) : #(D.Frames q C) = aleph 2 := by
  have hJ : #((aleph.{0} 2).ord.ToType) = aleph 2 := by rw [mk_toType, card_ord]
  exact (D.cardinal_frames q C (by rw [hJ]; exact aleph0_le_aleph 2) (by rwa [hJ])).trans hJ

end KnightModel.RankTwo.MarkedRows
