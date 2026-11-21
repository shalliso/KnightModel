import KnightModel.RankTwo.WalkSquareLimit
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular

/-! # Square ladders of width ω₁ on ω₂ have no thread -/

namespace KnightModel.RankTwo.SquareLadders

open Cardinal Ordinal Order Set

private abbrev J := (aleph.{0} 2).ord.ToType

private theorem cof_index : Order.cof J = aleph 2 := by
  have hr : Cardinal.IsRegular (aleph.{0} 2) := by
    simpa only [one_add_one_eq_two] using isRegular_aleph_add_one 1
  exact (Ordinal.cof_toType _).trans hr.cof_ord

/-- Above a point of a cofinal set there is a genuine limit of its elements.
Regularity keeps the countable increasing sequence below ω₂. -/
private theorem limit_above {D : Set J} (hc : IsCofinal D) (x : D) :
    ∃ b, x.val < b ∧ LadderLimit D b := by
  classical
  letI : NoMaxOrder J := Cardinal.noMaxOrder (aleph0_le_aleph 2)
  have next (t : D) : ∃ q : D, t.val < q.val := by
    obtain ⟨u,hu⟩ := exists_gt t.val
    obtain ⟨q,hq,huq⟩ := hc u
    exact ⟨⟨q,hq⟩,hu.trans_le huq⟩
  let f : ℕ → D := Nat.rec x fun _ t => (next t).choose
  have increases (n : ℕ) : (f n).val < (f (n+1)).val := (next (f n)).choose_spec
  let s : Set J := range (fun n => (f n).val)
  have bounded : BddAbove s := by
    apply BddAbove.of_not_isCofinal
    intro hs
    have large := Order.cof_le hs
    rw [cof_index] at large
    have small : #s ≤ ℵ₀ := Cardinal.mk_range_le.trans (by simp)
    have lt : ℵ₀ < aleph.{0} 2 := aleph0_lt_aleph_one.trans (aleph_lt_aleph.mpr one_lt_two)
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

/-- A cofinal subset of ω₂ cannot agree with every ladder at its positive
accumulation points. In particular the conventional no-club-thread clause of
Jensen square follows from the order-type bound. -/
theorem no_cofinal_thread (S : SquareLadders (aleph.{0} 2).ord.ToType (aleph.{0} 1).ord)
    {D : Set (aleph.{0} 2).ord.ToType} (hc : IsCofinal D) :
    ¬ ∀ b, (∃ n, n < b) → LadderLimit D b → S.ladder b = D ∩ Iio b := by
  intro thread
  have large : aleph 2 ≤ #D := cof_index.ge.trans (Order.cof_le hc)
  have wide : (aleph.{0} 1).ord < typeLT D :=
    (Cardinal.ord_lt_ord.mpr ((aleph_lt_aleph.mpr one_lt_two).trans_le large)).trans_le
      (Cardinal.ord_le_type LT.lt)
  let x : D := Ordinal.enum LT.lt ⟨(aleph.{0} 1).ord,wide⟩
  have hx : typeLT (Iio x) = (aleph.{0} 1).ord := Ordinal.typein_enum LT.lt wide
  obtain ⟨b,hxb,hlim⟩ := limit_above hc x
  have agrees := thread b ⟨x.val,hxb⟩ hlim
  have member {t : J} (hd : t ∈ D) (ht : t < b) : t ∈ S.ladder b := by
    rw [agrees]
    exact ⟨hd,ht⟩
  let y : S.ladder b := ⟨x.val,member x.property hxb⟩
  let emb (t : Iio x) : Iio y :=
    ⟨⟨t.val.val,member t.val.property (t.property.trans hxb)⟩,t.property⟩
  have hle : typeLT (Iio x) ≤ typeLT (Iio y) :=
    (RelEmbedding.ofMonotone (r := LT.lt) (s := LT.lt) emb (fun _ _ h => h)).ordinal_type_le
  have small : typeLT (Iio y) < (aleph.{0} 1).ord :=
    (Ordinal.typein_lt_type LT.lt y).trans_le (S.orderType_le b)
  exact (hx ▸ hle).not_gt small

theorem no_club_thread (S : SquareLadders (aleph.{0} 2).ord.ToType (aleph.{0} 1).ord) :
    ¬ ∃ D, IsClub D ∧ ∀ b, (∃ n, n < b) → LadderLimit D b → S.ladder b = D ∩ Iio b :=
  fun ⟨_,hc,h⟩ => S.no_cofinal_thread hc.isCofinal h

end KnightModel.RankTwo.SquareLadders

namespace KnightModel.RankTwo

open Cardinal Ordinal Order Set

/-- The public square hypothesis is equivalent to coherent clubs given only
at nonzero limits of ω₂, with the usual explicit prohibition of a club thread. -/
theorem squareAtOmegaOne_iff_threadless_limit_clubs :
    SquareAtOmegaOne ↔ ∃ S : LimitSquareLadders (aleph.{0} 2).ord.ToType (aleph.{0} 1).ord,
      ¬ ∃ D, IsClub D ∧ ∀ b (hb : IsSuccLimit b), LadderLimit D b → S.club b hb = D ∩ Iio b := by
  have hw : 1 ≤ (aleph.{0} 1).ord := by
    rw [ord_aleph, Order.one_le_iff_ne_zero]
    exact (Ordinal.omega_pos 1).ne'
  have he := limitSquare_iff_square (J := (aleph.{0} 2).ord.ToType) _ hw
  refine ⟨fun hs => ?_, fun ⟨S,_⟩ => he.mp ⟨S⟩⟩
  obtain ⟨S⟩ := he.mpr hs
  refine ⟨S,?_⟩
  rintro ⟨D,hc,thread⟩
  apply (S.complete hw).no_cofinal_thread hc.isCofinal
  intro b hpos hlim
  have hb : IsSuccLimit b := by
    obtain ⟨p,hp⟩ := hpos
    refine ⟨not_isMin_of_lt hp,?_⟩
    intro x hx
    obtain ⟨t,_,hxt,htb⟩ := hlim x hx.lt
    exact hxt.not_ge (hx.le_of_lt htb)
  exact (S.fill_limit hb).trans (thread b hb hlim)

end KnightModel.RankTwo
