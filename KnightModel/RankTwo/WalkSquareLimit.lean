import KnightModel.RankTwo.WalkSquare
import Mathlib.Order.SuccPred.Limit

/-! # Supplying square clubs only at nonzero limit ordinals -/

namespace KnightModel.RankTwo

open Set Ordinal Order

universe u

/-- The usual coherent clubs, indexed only by nonzero limit points of the
index well-order. The no-thread clause is unnecessary for the construction. -/
structure LimitSquareLadders (J : Type u) [LinearOrder J] [WellFoundedLT J] (width : Ordinal.{u}) where
  club : (b : J) → IsSuccLimit b → Set J
  below : ∀ {b} (hb : IsSuccLimit b) {x}, x ∈ club b hb → x < b
  cofinal : ∀ {b} (hb : IsSuccLimit b) {x}, x < b → ∃ t ∈ club b hb, x ≤ t
  closed : ∀ {b d} (hb : IsSuccLimit b) (_ : IsSuccLimit d), d < b →
    LadderLimit (club b hb) d → d ∈ club b hb
  coherent : ∀ {b d} (hb : IsSuccLimit b) (hd : IsSuccLimit d), d < b →
    LadderLimit (club b hb) d → club d hd = club b hb ∩ Iio d
  orderType_le : ∀ b (hb : IsSuccLimit b), typeLT (club b hb) ≤ width

namespace LimitSquareLadders

variable {J : Type u} [LinearOrder J] [WellFoundedLT J] {width : Ordinal.{u}}
variable (S : LimitSquareLadders J width)

/-- At a successor the only added point is its predecessor. At the least
element there is no predecessor to add. -/
noncomputable def fill (b : J) : Set J := by
  classical
  exact if hb : IsSuccLimit b then S.club b hb else {p | p ⋖ b}

theorem fill_limit {b : J} (hb : IsSuccLimit b) : S.fill b = S.club b hb := by
  classical
  simp [fill, hb]

theorem fill_other {b : J} (hb : ¬IsSuccLimit b) : S.fill b = {p | p ⋖ b} := by
  classical
  simp [fill, hb]

omit [WellFoundedLT J] in
private theorem limit_index {c : Set J} {d : J} (positive : ∃ n, n < d) (h : LadderLimit c d) :
    IsSuccLimit d := by
  obtain ⟨n, hn⟩ := positive
  refine ⟨not_isMin_of_lt hn, ?_⟩
  intro p hp
  obtain ⟨t, _, hpt, htd⟩ := h p hp.lt
  exact (not_le_of_gt hpt) (hp.le_of_lt htd)

private theorem parent_limit {b d : J} (positive : ∃ n, n < d) (h : LadderLimit (S.fill b) d) :
    IsSuccLimit b := by
  by_contra hb
  rw [S.fill_other hb] at h
  obtain ⟨n, hnd⟩ := positive
  obtain ⟨t, ht, _, htd⟩ := h n hnd
  obtain ⟨q, hq, htq, _⟩ := h t htd
  change t ⋖ b at ht
  change q ⋖ b at hq
  exact (not_le_of_gt htq) (ht.le_of_lt hq.lt)

/-- Adding the customary successor ladders produces precisely the square
input used by the walk construction. -/
noncomputable def complete (hw : 1 ≤ width) : SquareLadders J width where
  ladder := S.fill
  below := by
    intro b x hx
    by_cases hb : IsSuccLimit b
    · rw [S.fill_limit hb] at hx
      exact S.below hb hx
    · rw [S.fill_other hb] at hx
      exact (show x ⋖ b from hx).lt
  cofinal := by
    intro x b hxb
    by_cases hb : IsSuccLimit b
    · rw [S.fill_limit hb]
      exact S.cofinal hb hxb
    · rw [S.fill_other hb]
      have hs : ¬IsSuccPrelimit b := fun hs => hb ⟨not_isMin_of_lt hxb, hs⟩
      obtain ⟨p, hp⟩ := not_isSuccPrelimit_iff.mp hs
      exact ⟨p, hp, hp.le_of_lt hxb⟩
  closed := by
    intro b d hdb hpos hlim
    have hb := S.parent_limit hpos hlim
    have hd := limit_index hpos hlim
    rw [S.fill_limit hb] at hlim ⊢
    exact S.closed hb hd hdb hlim
  coherent := by
    intro b d hdb hpos hlim
    have hb := S.parent_limit hpos hlim
    have hd := limit_index hpos hlim
    rw [S.fill_limit hb] at hlim ⊢
    rw [S.fill_limit hd]
    exact S.coherent hb hd hdb hlim
  orderType_le := by
    intro b
    by_cases hb : IsSuccLimit b
    · rw [S.fill_limit hb]
      exact S.orderType_le b hb
    · rw [S.fill_other hb]
      let P := {p : J // p ⋖ b}
      haveI : Subsingleton P := ⟨fun x y => Subtype.ext ((x.2.le_of_lt y.2.lt).antisymm
        (y.2.le_of_lt x.2.lt)).symm⟩
      change type (α := P) (· < ·) ≤ width
      rcases isEmpty_or_nonempty P with he | hn
      · rw [type_eq_zero_iff_isEmpty.mpr he]
        exact zero_le
      · letI := hn
        rwa [type_eq_one_of_unique]

end LimitSquareLadders

/-- Using only limit indices or all indices gives the same square assumption. -/
theorem limitSquare_iff_square {J : Type u} [LinearOrder J] [WellFoundedLT J]
    (width : Ordinal.{u}) (hw : 1 ≤ width) :
    Nonempty (LimitSquareLadders J width) ↔ Nonempty (SquareLadders J width) := by
  refine ⟨fun ⟨S⟩ => ⟨S.complete hw⟩, ?_⟩
  rintro ⟨S⟩
  exact ⟨{
    club := fun b _ => S.ladder b
    below := fun _ => S.below
    cofinal := fun _ => S.cofinal
    closed := fun _ hd hdb => S.closed hdb hd.nonempty_Iio
    coherent := fun _ hd hdb => S.coherent hdb hd.nonempty_Iio
    orderType_le := fun b _ => S.orderType_le b }⟩

end KnightModel.RankTwo
