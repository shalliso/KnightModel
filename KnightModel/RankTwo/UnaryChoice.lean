import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Invariant choice on the line

A finite cover by monochromatic interval cells yields a point fixed by every
symmetry of a nonempty set. Only lower endpoints of cells need to be specified.
The construction uses the first endpoint of the set or its complement and,
for an open left endpoint, the first subsequent point of the complement.
-/

namespace KnightModel.RankTwo

open Set

namespace UnaryChoice

variable {V : Type*} [LinearOrder V]

/-- A cell has a possibly infinite left endpoint. Between this endpoint and
each of its members it contains every point. -/
structure Cell (V : Type*) [LinearOrder V] where
  carrier : Set V
  lower : Option V
  bound : ∀ a, lower = some a → ∀ x ∈ carrier, a ≤ x
  fill : ∀ x ∈ carrier, ∀ y < x, (∀ a, lower = some a → a < y) → y ∈ carrier

/-- A finite interval decomposition, with arbitrary endpoint conventions.
The same cover works for the complement. -/
def Decomposed (S : Set V) : Prop :=
  ∃ cs : List (Cell V), (∀ x, ∃ c ∈ cs, x ∈ c.carrier) ∧
    ∀ c ∈ cs, c.carrier ⊆ S ∨ c.carrier ⊆ Sᶜ

private def StartsAt (S : Set V) (a : V) : Prop :=
  a ∈ lowerBounds S ∧ (a ∈ S ∨ ∃ b > a, Ioo a b ⊆ S)

private def Starts (S : Set V) : Prop :=
  S = ∅ ∨ (∃ b, Iio b ⊆ S) ∨ ∃ a, StartsAt S a

private theorem startsAt_mono {S T : Set V} {a : V} (h : StartsAt S a)
    (sub : S ⊆ T) (lo : a ∈ lowerBounds T) : StartsAt T a :=
  ⟨lo, h.2.imp (fun ha => sub ha) (fun ⟨b,hb,hi⟩ => ⟨b,hb,hi.trans sub⟩)⟩

private theorem starts_union {S T : Set V} (hS : Starts S) (hT : Starts T) :
    Starts (S ∪ T) := by
  rcases hS with rfl | ⟨b, hb⟩ | ⟨a, ha⟩
  · simpa using hT
  · exact .inr (.inl ⟨b, hb.trans subset_union_left⟩)
  rcases hT with rfl | ⟨b, hb⟩ | ⟨b, hb⟩
  · simpa [Starts] using (show Starts S from .inr (.inr ⟨a, ha⟩))
  · exact .inr (.inl ⟨b, hb.trans subset_union_right⟩)
  · apply Or.inr ∘ Or.inr
    rcases le_total a b with h | h
    · exact ⟨a, startsAt_mono ha subset_union_left (fun x hx => hx.elim (ha.1 ·) (fun t => h.trans (hb.1 t)))⟩
    · exact ⟨b, startsAt_mono hb subset_union_right (fun x hx => hx.elim (fun t => h.trans (ha.1 t)) (hb.1 ·))⟩

private theorem cell_starts (c : Cell V) : Starts c.carrier := by
  rcases c.carrier.eq_empty_or_nonempty with he | ⟨x, hx⟩
  · exact .inl he
  cases h : c.lower with
  | none => exact .inr (.inl ⟨x, fun y hy => c.fill x hx y hy (by simp [h])⟩)
  | some a =>
    refine .inr (.inr ⟨a, fun x hx => c.bound a h x hx, ?_⟩)
    rcases (c.bound a h x hx).lt_or_eq with hax | rfl
    · exact .inr ⟨x, hax, fun y hy => c.fill x hx y hy.2 (by simpa [h] using hy.1)⟩
    · exact .inl hx

private def above (c : Cell V) (a : V) : Cell V where
  carrier := c.carrier ∩ Ioi a
  lower := some (c.lower.elim a (max a))
  bound b hb x hx := by
    cases h : c.lower with
    | none => simp [h] at hb; exact hb ▸ hx.2.le
    | some l => simp [h] at hb; exact hb ▸ max_le hx.2.le (c.bound _ h _ hx.1)
  fill x hx y hy hl := by
    have h := hl _ rfl
    cases hc : c.lower with
    | none =>
      simp [hc] at h
      exact ⟨c.fill _ hx.1 _ hy (by simp [hc]), h⟩
    | some l =>
      simp [hc] at h
      exact ⟨c.fill _ hx.1 _ hy (by simpa [hc] using h.2), h.1⟩

private theorem starts_from_cover (cs : List (Cell V)) (S : Set V) (f : Cell V → Set V)
    (hf : ∀ c, Starts (f c)) (cover : S = {x | ∃ c ∈ cs, x ∈ f c}) : Starts S := by
  subst S
  induction cs with
  | nil => exact Or.inl (by ext; simp)
  | cons c cs ih =>
    convert starts_union (hf c) ih using 1
    ext; simp [or_and_right, exists_or]

private theorem starts_query {S : Set V} (hD : Decomposed S) (Q : Set V)
    (hQ : Q = S ∨ Q = Sᶜ) (a : Option V) :
    Starts {x | x ∈ Q ∧ ∀ b, a = some b → b < x} := by
  classical
  obtain ⟨cs, cover, colors⟩ := hD
  let part (c : Cell V) := a.elim c (above c)
  have hp (c : Cell V) (x : V) :
      x ∈ (part c).carrier ↔ x ∈ c.carrier ∧ ∀ b, a = some b → b < x := by
    cases a <;> simp [part, above, Set.mem_Ioi]
  let f (c : Cell V) := if c.carrier ⊆ Q then (part c).carrier else ∅
  apply starts_from_cover cs _ f
  · intro c
    dsimp [f]; split
    · exact cell_starts _
    · exact Or.inl rfl
  · ext x
    constructor
    · rintro ⟨hx, ha⟩
      obtain ⟨c, hc, hxc⟩ := cover x
      have sub : c.carrier ⊆ Q := by
        rcases hQ with rfl | rfl <;> obtain hs | ht := colors c hc
        · exact hs
        · exact ((ht hxc) hx).elim
        · exact (hx (hs hxc)).elim
        · exact ht
      exact ⟨c, hc, by simpa [f, sub] using (hp c x).mpr ⟨hxc, ha⟩⟩
    · rintro ⟨c, _, hx⟩
      by_cases h : c.carrier ⊆ Q
      · have hh := (hp c x).mp (by simpa [f, h] using hx)
        exact ⟨h hh.1, hh.2⟩
      · simp [f, h] at hx

/-- The endpoints and a point strictly between two endpoints can be used by
any order automorphism commuting with these choices. In the vector group
these are translation by ±d, the midpoint, and the zero vector. -/
structure Samples (V : Type*) [LT V] where
  base : V
  down : V → V
  up : V → V
  mid : V → V → V
  down_lt : ∀ v, down v < v
  lt_up : ∀ v, v < up v
  between : ∀ a b, a < b → a < mid a b ∧ mid a b < b

structure Preserves {P : Samples V} (e : V ≃o V) : Prop where
  base : e P.base = P.base
  down : ∀ x, e (P.down x) = P.down (e x)
  up : ∀ x, e (P.up x) = P.up (e x)
  mid : ∀ x y, e (P.mid x y) = P.mid (e x) (e y)

private theorem startsAt_glb [DenselyOrdered V] {S : Set V} {a : V}
    (h : StartsAt S a) : IsGLB S a := by
  refine ⟨h.1, fun b hb => ?_⟩
  rcases h.2 with ha | ⟨t, ht, hseg⟩
  · exact hb ha
  · by_contra! hh
    obtain ⟨y, hy, hy'⟩ := exists_between (lt_min hh ht)
    exact (hb (hseg ⟨hy, hy'.trans_le (min_le_right _ _)⟩)).not_gt
      (hy'.trans_le (min_le_left _ _))

private theorem fixed_glb {S : Set V} {a : V} (glb : IsGLB S a) (e : V ≃o V)
    (invar : ∀ x, x ∈ S ↔ e x ∈ S) : e a = a := by
  apply le_antisymm
  · exact glb.2 (fun x hx => by
      have ht : e.symm x ∈ S := (invar _).mpr (by simpa)
      simpa using e.monotone (glb.1 ht))
  · apply e.symm.le_iff_le.mp
    simp only [OrderIso.symm_apply_apply]
    exact glb.2 fun x hx => e.le_iff_le.mp (by simpa using glb.1 ((invar x).mp hx))

/-- A nonempty finite union of interval cells has a point invariant under its
setwise stabilizer in the group of sample-preserving order automorphisms. -/
theorem exists_fixed [DenselyOrdered V] (P : Samples V) {S : Set V}
    (dec : Decomposed S) (hne : S.Nonempty) :
    ∃ z ∈ S, ∀ e : V ≃o V, Preserves (P := P) e → (∀ x, x ∈ S ↔ e x ∈ S) → e z = z := by
  classical
  have starts (Q : Set V) (h : Q = S ∨ Q = Sᶜ) : Starts Q := by
    simpa using starts_query dec Q h none
  rcases starts S (Or.inl rfl) with hem | ⟨t, ht⟩ | ⟨a, ha⟩
  · exact (hne.ne_empty hem).elim
  · rcases starts Sᶜ (Or.inr rfl) with hem | ⟨u, hu⟩ | ⟨b, hb⟩
    · refine ⟨P.base, ?_, fun e hp _ => hp.base⟩
      by_contra hn
      exact (hem ▸ (show P.base ∈ Sᶜ from hn) : P.base ∈ (∅ : Set V))
    · exact ((hu ((P.down_lt _).trans_le (min_le_right _ _))) (ht
        ((P.down_lt _).trans_le (min_le_left _ _)))).elim
    · refine ⟨P.down b, ?_, fun e he hs => ?_⟩
      · by_contra h
        exact (P.down_lt b).not_ge (hb.1 h)
      · rw [he.down, fixed_glb (startsAt_glb hb) e (fun x => (hs x).not)]
  · have fixA (e : V ≃o V) (h : ∀ x, x ∈ S ↔ e x ∈ S) :=
      fixed_glb (startsAt_glb ha) e h
    rcases ha.2 with hmem | ⟨t, hat, ht⟩
    · exact ⟨a, hmem, fun e _ h => fixA e h⟩
    let U := {x : V | x ∉ S ∧ a < x}
    have ustart : Starts U := by simpa [U] using starts_query dec Sᶜ (.inr rfl) (some a)
    rcases ustart with hem | ⟨u, hu⟩ | ⟨b, hb⟩
    · refine ⟨P.up a, ?_, fun e he hs => ?_⟩
      · by_contra h
        have hx : P.up a ∈ U := ⟨h, P.lt_up a⟩
        exact (hem ▸ hx : P.up a ∈ (∅ : Set V))
      · rw [he.up, fixA e hs]
    · have hx := hu (show P.down (min u a) < u from (P.down_lt _).trans_le (min_le_left _ _))
      exact (hx.2.not_gt ((P.down_lt _).trans_le (min_le_right _ _))).elim
    · have htb : t ≤ b := (startsAt_glb hb).2 (fun x hx => le_of_not_gt
        (fun hxt => hx.1 (ht ⟨hx.2, hxt⟩)))
      obtain ⟨hleft, hright⟩ := P.between a b (hat.trans_le htb)
      refine ⟨P.mid a b, ?_, fun e he hs => ?_⟩
      · by_contra h
        exact hright.not_ge (hb.1 (show P.mid a b ∈ U from ⟨h, hleft⟩))
      · have hf := fixA e hs
        have hu (x : V) : x ∈ U ↔ e x ∈ U := by
          change (_ ∧ a < x) ↔ (_ ∧ a < e x)
          exact and_congr (hs x).not (by simpa only [hf] using (e.lt_iff_lt (x := a) (y := x)).symm)
        rw [he.mid, hf, fixed_glb (startsAt_glb hb) e hu]

end UnaryChoice
end KnightModel.RankTwo
