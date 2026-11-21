import KnightModel.RankTwo.Walk
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Square ladders supply coherent walk labels

Only closure, cofinality, coherence of restrictions and the order-type bound
are needed.  In particular, none of the walk lemmas assumes a thread or an
embedding of the skeleton as extra data.
-/

namespace KnightModel.RankTwo

open Ordinal Set

universe u v

/-- Square data on a well-ordered index type. Successor ladders may be taken to
be the singleton predecessor; the walk construction works with any cofinal
subset of the strict initial segment there. -/
structure SquareLadders (J : Type u) [LinearOrder J] [WellFoundedLT J] (width : Ordinal.{u}) where
  ladder : J → Set J
  below : ∀ {b x}, x ∈ ladder b → x < b
  cofinal : ∀ {g b}, g < b → ∃ x ∈ ladder b, g ≤ x
  closed : ∀ {b d}, d < b → (∃ n, n < d) → LadderLimit (ladder b) d → d ∈ ladder b
  coherent : ∀ {b d}, d < b → (∃ n, n < d) → LadderLimit (ladder b) d →
    ladder d = ladder b ∩ Iio d
  orderType_le : ∀ b, typeLT (ladder b) ≤ width

namespace SquareLadders

variable {J : Type u} {A : Type v} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable {width : Ordinal.{u}} (S : SquareLadders J width)

/-- The slot of a visited vertex is strictly below the width, even when the
whole ladder has order type equal to the width. -/
noncomputable def position (b : J) (x : S.ladder b) : Iio width :=
  ⟨Ordinal.typein LT.lt x, (Ordinal.typein_lt_type LT.lt x).trans_le (S.orderType_le b)⟩

theorem position_strictMono (b : J) : StrictMono (S.position b) :=
  fun _ _ h => (Ordinal.typein_lt_typein LT.lt).mpr h

/-- The order type before a member is unchanged upon restriction to a
coherent ladder containing it. -/
theorem position_coherent {b d x : J} (hdb : d < b) (hpos : ∃ n, n < d)
    (hlim : LadderLimit (S.ladder b) d) (hx : x < d)
    (hb : x ∈ S.ladder b) (hd : x ∈ S.ladder d) :
    S.position b ⟨x, hb⟩ = S.position d ⟨x, hd⟩ := by
  have hc := S.coherent hdb hpos hlim
  have restrict (z : J) : z ∈ S.ladder d ↔ z ∈ S.ladder b ∧ z < d := by
    rw [hc]
    rfl
  let E : Iio (⟨x, hb⟩ : S.ladder b) ≃o Iio (⟨x, hd⟩ : S.ladder d) :=
    { toEquiv :=
        { toFun := fun y => ⟨⟨y.val.val, (restrict _).mpr ⟨y.val.property, y.property.trans hx⟩⟩,
              y.property⟩
          invFun := fun y => ⟨⟨y.val.val, ((restrict _).mp y.val.property).1⟩, y.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  apply Subtype.ext
  exact E.ordinalType_congr

/-- Relabel the intrinsic ordinal slots by any increasing family of letters. -/
noncomputable def labelled (mark : Iio width ↪o A) : CoherentLadders J A where
  ladder := S.ladder
  below := S.below
  cofinal := S.cofinal
  label b x := mark (S.position b x)
  label_strictMono b := mark.strictMono.comp (S.position_strictMono b)
  closed := S.closed
  coherent := by
    intro b d hdb hp hl x hx
    rw [S.coherent hdb hp hl]
    exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  label_coherent := by
    intro b d hdb hp hl x hx hb hd
    exact congrArg mark (S.position_coherent hdb hp hl hx hb hd)

end SquareLadders

/-- The coherent square-ladder hypothesis at the cardinals of the construction. -/
abbrev SquareAtOmegaOne : Prop :=
  Nonempty (SquareLadders (Cardinal.aleph.{0} 2).ord.ToType (Cardinal.aleph.{0} 1).ord)

end KnightModel.RankTwo
