import KnightModel.Transfinite.Tower
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular

/-! # Conventional Jensen square at the successor of an infinite cardinal

The bound on the order types excludes club threads for singular and regular widths alike.
-/

namespace KnightModel.Transfinite

open RankTwo Cardinal Ordinal Order Set

variable {κ : Cardinal.{0}}

private theorem cof_index (hκ : ℵ₀ ≤ κ) : Order.cof (AtlasIndex κ) = succ κ :=
  (Ordinal.cof_toType _).trans (isRegular_succ hκ).cof_ord

/-- Above a point of a cofinal set there is a genuine limit of its elements.
Regularity keeps the countable increasing sequence below κ⁺. -/
private theorem limit_above (hκ : ℵ₀ ≤ κ) {D : Set (AtlasIndex κ)} (hc : IsCofinal D) (x : D) :
    ∃ b, x.val < b ∧ LadderLimit D b := by
  classical
  letI : NoMaxOrder (AtlasIndex κ) := Cardinal.noMaxOrder (hκ.trans (le_succ κ))
  have next (t : D) : ∃ q : D, t.val < q.val := by
    obtain ⟨u,hu⟩ := exists_gt t.val
    obtain ⟨q,hq,huq⟩ := hc u
    exact ⟨⟨q,hq⟩,hu.trans_le huq⟩
  let f : ℕ → D := Nat.rec x fun _ t => (next t).choose
  have increases (n : ℕ) : (f n).val < (f (n+1)).val := (next (f n)).choose_spec
  let s : Set (AtlasIndex κ) := range (fun n => (f n).val)
  have bounded : BddAbove s := by
    apply BddAbove.of_not_isCofinal
    intro hs
    have large := Order.cof_le hs
    rw [cof_index hκ] at large
    have small : #s ≤ ℵ₀ := Cardinal.mk_range_le.trans (by simp)
    have lt : ℵ₀ < succ κ := hκ.trans_lt (lt_succ κ)
    exact lt.not_ge (large.trans small)
  obtain ⟨b,hb,hmin⟩ := wellFounded_lt.has_min (upperBounds s) bounded
  have below (n : ℕ) : (f n).val < b :=
    (increases n).trans_le (hb (mem_range_self (n+1)))
  refine ⟨b,below 0,?_⟩
  intro u hub
  have hn : ¬ u ∈ upperBounds s := fun hu => hmin u hu hub
  change ¬ ∀ ⦃t⦄, t ∈ s → t ≤ u at hn
  push Not at hn
  obtain ⟨t,ht,htu⟩ := hn
  obtain ⟨n,rfl⟩ := ht
  exact ⟨_,(f n).property,htu,below n⟩

/-- A cofinal subset of κ⁺ cannot agree with every ladder at its positive
accumulation points. In particular the conventional no-club-thread clause of
Jensen square follows from the order-type bound. -/
theorem no_cofinal_square_thread (hκ : ℵ₀ ≤ κ) (S : SquareLadders (AtlasIndex κ) κ.ord)
    {D : Set (AtlasIndex κ)} (hc : IsCofinal D) :
    ¬ ∀ b, (∃ n, n < b) → LadderLimit D b → S.ladder b = D ∩ Iio b := by
  intro thread
  have large : succ κ ≤ #D := (cof_index hκ).ge.trans (Order.cof_le hc)
  have wide : κ.ord < typeLT D :=
    (Cardinal.ord_lt_ord.mpr ((lt_succ κ).trans_le large)).trans_le
      (Cardinal.ord_le_type LT.lt)
  let x : D := Ordinal.enum LT.lt ⟨κ.ord,wide⟩
  have hx : typeLT (Iio x) = κ.ord := Ordinal.typein_enum LT.lt wide
  obtain ⟨b,hxb,hlim⟩ := limit_above hκ hc x
  have agrees := thread b ⟨x.val,hxb⟩ hlim
  have member {t : AtlasIndex κ} (hd : t ∈ D) (ht : t < b) : t ∈ S.ladder b := by
    rw [agrees]
    exact ⟨hd,ht⟩
  let y : S.ladder b := ⟨x.val,member x.property hxb⟩
  let emb (t : Iio x) : Iio y :=
    ⟨⟨t.val.val,member t.val.property (t.property.trans hxb)⟩,t.property⟩
  have hle : typeLT (Iio x) ≤ typeLT (Iio y) :=
    (RelEmbedding.ofMonotone (r := LT.lt) (s := LT.lt) emb (fun _ _ h => h)).ordinal_type_le
  have small : typeLT (Iio y) < κ.ord :=
    (Ordinal.typein_lt_type LT.lt y).trans_le (S.orderType_le b)
  exact (hx ▸ hle).not_gt small

/-- The club-sequence form of Jensen square, supplying clubs only at nonzero
limits and expressly forbidding a club thread. -/
def JensenSquare (κ : Cardinal.{0}) : Prop :=
  ∃ S : LimitSquareLadders (AtlasIndex κ) κ.ord,
    ¬ ∃ D, IsClub D ∧ ∀ b (hb : IsSuccLimit b), LadderLimit D b → S.club b hb = D ∩ Iio b

/-- The exact hypothesis for the word atlas is equivalent to Jensen square. -/
theorem jensenSquare_iff (hκ : ℵ₀ ≤ κ) : JensenSquare κ ↔
    Nonempty (SquareLadders (AtlasIndex κ) κ.ord) := by
  symm
  have hw : 1 ≤ κ.ord := Cardinal.ord_one ▸ Cardinal.ord_le_ord.mpr (one_le_aleph0.trans hκ)
  have he := limitSquare_iff_square (J := AtlasIndex κ) _ hw
  refine ⟨fun hs => ?_, fun ⟨S,_⟩ => he.mp ⟨S⟩⟩
  obtain ⟨S⟩ := he.mpr hs
  refine ⟨S,?_⟩
  rintro ⟨D,hc,thread⟩
  apply no_cofinal_square_thread hκ (S.complete hw) hc.isCofinal
  intro b hpos hlim
  have hb : IsSuccLimit b := by
    obtain ⟨p,hp⟩ := hpos
    refine ⟨not_isMin_of_lt hp,?_⟩
    intro x hx
    obtain ⟨t,_,hxt,htb⟩ := hlim x hx.lt
    exact hxt.not_ge (hx.le_of_lt htb)
  exact (S.fill_limit hb).trans (thread b hb hlim)

/-- The family of internal ladder assumptions used by the tower is exactly
Jensen square at each indicated aleph. -/
theorem squaresBelow_iff_jensenSquare (α : Ordinal.{0}) :
    SquaresBelow α ↔ ∀ β < α, JensenSquare (aleph β) :=
  ⟨fun hs β hb => (jensenSquare_iff (aleph0_le_aleph β)).mpr (hs β hb),
   fun hs β hb => (jensenSquare_iff (aleph0_le_aleph β)).mp (hs β hb)⟩

end KnightModel.Transfinite
