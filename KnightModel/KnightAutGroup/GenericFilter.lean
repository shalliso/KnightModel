/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.DenseSets

/-!
# Generic Filter for the Knight Group Construction

Applies the Rasiowa–Sikorski theorem (`Order.idealOfCofinals`) to produce a generic filter
of `KnightCondition`s meeting all four families of dense open sets from `DenseSets.lean`.
From this filter we extract the generic automorphisms `genericAut n : ℚ ≃o ℚ`.

## Main definitions

* `DenseIdx`: index type encoding all four dense families.
* `denseSets`: packages each family as an `Order.Cofinal KnightConditionᵒᵈ`.
* `genericIdeal` / `genericFilter`: the ideal and filter produced by Rasiowa–Sikorski.
* `genericPartialIso n`: the union of `(p.seq n).graph` over the filter — a total `PartialIso`.
* `genericAut n`: the `n`-th generic automorphism, obtained by totaling `genericPartialIso n`.

## Main results

* `genericFilter_meets_inDomain`, `…inRange`, `…connects`, `…decrements`:
  the filter meets every relevant dense set.
* `genericAut_spec`: if `p ∈ genericFilter` has `(a, b) ∈ (p.seq n).graph`,
  then `genericAut n a = b`.
* `exists_extension_with_domain`: given a word and a point, some filter element brings
  all generator indices in the word into the domain.

## Tags

generic filter, Rasiowa–Sikorski, forcing, generic automorphism
-/

section GenericFilter

open OrderDual

/-- Index type for the countable family of dense open sets.
    Encoded as `(inDomain params) ⊕ (inRange params) ⊕ (connects params) ⊕ (decrements params)`.
    Since `ℕ` and `ℚ` are both `Encodable`, each summand (and hence the sum) is `Encodable`. -/
abbrev DenseIdx := (ℕ × ℚ) ⊕ (ℕ × ℚ) ⊕ (ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ)

/-- Lift a density witness `∀ p, ∃ q ≤ p, q ∈ S` into an `Order.Cofinal KnightConditionᵒᵈ`. -/
private def toCofinalDual (S : Set KnightCondition)
    (hdense : ∀ p : KnightCondition, ∃ q ∈ S, q ≤ p) :
    Order.Cofinal KnightConditionᵒᵈ where
  carrier   := ofDual ⁻¹' S
  -- For every `x : KnightConditionᵒᵈ`, find `y ∈ S` with `x ≤ᵒᵈ y` (i.e. y ≤ ofDual x).
  isCofinal := fun x => by
    obtain ⟨q, hqS, hqx⟩ := hdense (ofDual x)
    -- hqx : q ≤ ofDual x  ↔  x ≤ᵒᵈ toDual q  (by definition of the dual order)
    exact ⟨toDual q, hqS, hqx⟩

/-- Package each dense open set as a `Cofinal KnightConditionᵒᵈ`.
    For `decrements a b c` with `¬(a < b ∧ b < c)` we use the trivially cofinal set `univ`. -/
noncomputable def denseSets : DenseIdx → Order.Cofinal KnightConditionᵒᵈ
  | .inl (n, a)                    =>
      toCofinalDual _ (fun p => by obtain ⟨q, hq, hmq⟩ := KnightCondition.inDomain_dense n a p
                                   exact ⟨q, hmq, hq⟩)
  | .inr (.inl (n, a))             =>
      toCofinalDual _ (fun p => by obtain ⟨q, hq, hmq⟩ := KnightCondition.inRange_dense n a p
                                   exact ⟨q, hmq, hq⟩)
  | .inr (.inr (.inl (a, b)))      =>
      toCofinalDual _ (fun p => by obtain ⟨q, hq, hmq⟩ := KnightCondition.connects_dense a b p
                                   exact ⟨q, hmq, hq⟩)
  | .inr (.inr (.inr (a, b, c)))   =>
      if h : a < b ∧ b < c then
        toCofinalDual _ (fun p => by
          obtain ⟨q, hq, hmq⟩ := KnightCondition.decrements_dense a b c h.1 h.2 p
          exact ⟨q, hmq, hq⟩)
      else
        -- Trivially cofinal: everything is in `univ`
        { carrier := Set.univ, isCofinal := fun x => ⟨x, Set.mem_univ _, le_refl _⟩ }

/-! ### The generic ideal and filter -/

/-- The generic ideal on `KnightConditionᵒᵈ`: an `Order.Ideal` meeting all `denseSets`.
    Constructed by the Rasiowa–Sikorski lemma (`Order.idealOfCofinals`). -/
noncomputable def genericIdeal : Order.Ideal KnightConditionᵒᵈ :=
  Order.idealOfCofinals (toDual (∅ : KnightCondition)) denseSets

/-- The generic filter: the corresponding set of `KnightCondition`s. -/
noncomputable def genericFilter : Set KnightCondition :=
  ofDual ⁻¹' (genericIdeal : Set KnightConditionᵒᵈ)

/-- The empty condition belongs to the generic filter. -/
lemma mem_genericFilter_empty : (∅ : KnightCondition) ∈ genericFilter := by
  change toDual (∅ : KnightCondition) ∈ genericIdeal
  exact Order.mem_idealOfCofinals _ _

/-- The generic filter is upward-closed under weakening:
    if `p ∈ genericFilter` and `p ≤ q` (p extends q, q is weaker), then `q ∈ genericFilter`. -/
lemma genericFilter_upward {p q : KnightCondition}
    (hp : p ∈ genericFilter) (hpq : p ≤ q) : q ∈ genericFilter :=
  genericIdeal.lower hpq hp

/-- Any two conditions in the generic filter have a common extension in the filter. -/
lemma genericFilter_directed {p q : KnightCondition}
    (hp : p ∈ genericFilter) (hq : q ∈ genericFilter) :
    ∃ r ∈ genericFilter, r ≤ p ∧ r ≤ q := by
  obtain ⟨c, hc, hpc, hqc⟩ := Order.Ideal.directed genericIdeal p hp q hq
  exact ⟨c, hc, hpc, hqc⟩

/-! ### Density: the generic filter meets each dense open set -/

/-- The generic filter meets every `inDomain n a`. -/
lemma genericFilter_meets_inDomain (n : ℕ) (a : ℚ) :
    ∃ p ∈ genericFilter, p ∈ KnightCondition.inDomain n a := by
  obtain ⟨x, hx, hxG⟩ :=
    Order.cofinal_meets_idealOfCofinals (toDual (∅ : KnightCondition)) denseSets (.inl (n, a))
  exact ⟨ofDual x, hxG, hx⟩

/-- The generic filter meets every `inRange n a`. -/
lemma genericFilter_meets_inRange (n : ℕ) (a : ℚ) :
    ∃ p ∈ genericFilter, p ∈ KnightCondition.inRange n a := by
  obtain ⟨x, hx, hxG⟩ :=  Order.cofinal_meets_idealOfCofinals
    (toDual (∅ : KnightCondition)) denseSets (.inr (.inl (n, a)))
  exact ⟨ofDual x, hxG, hx⟩

/-- The generic filter meets every `connects a b`. -/
lemma genericFilter_meets_connects (a b : ℚ) :
    ∃ p ∈ genericFilter, p ∈ KnightCondition.connects a b := by
  obtain ⟨x, hx, hxG⟩ :=
    Order.cofinal_meets_idealOfCofinals (toDual (∅ : KnightCondition)) denseSets
      (.inr (.inr (.inl (a, b))))
  exact ⟨ofDual x, hxG, hx⟩

/-- The generic filter meets every `decrements a b c` when `a < b < c`. -/
lemma genericFilter_meets_decrements (a b c : ℚ) (hab : a < b) (hbc : b < c) :
    ∃ p ∈ genericFilter, p ∈ KnightCondition.decrements a b c := by
  obtain ⟨x, hx, hxG⟩ :=
    Order.cofinal_meets_idealOfCofinals (toDual (∅ : KnightCondition)) denseSets
      (.inr (.inr (.inr (a, b, c))))
  simp only [denseSets] at hx
  rw [dif_pos ⟨hab, hbc⟩] at hx
  exact ⟨ofDual x, hxG, hx⟩

end GenericFilter

/-! ## Generic Automorphisms

For each `n : ℕ`, we define `genericAut n : ℚ ≃o ℚ` by taking the union of the graphs
`(p.seq n).graph` over all `p ∈ genericFilter`, proving the result is a total order-isomorphism,
and applying `PartialIso.toIso`. -/

section GenericAut

open OrderDual

/-- The union of graphs of the `n`-th partial automorphism over all conditions in the
    generic filter.  This is a total `PartialIso ℚ ℚ`. -/
noncomputable def genericPartialIso (n : ℕ) : PartialIso ℚ ℚ where
  graph := ⋃ p ∈ genericFilter, (p.seq n).graph
  functional := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' haa'
    simp only [Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ := genericFilter_directed hP hQ
    simp only at haa'
    subst haa'
    exact (r.seq n).toPartialIso.functional _ (hrP n hPab) _ (hrQ n hQab) rfl
  injective := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' hbb'
    simp only [Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ := genericFilter_directed hP hQ
    simp only at hbb'
    subst hbb'
    exact (r.seq n).toPartialIso.injective _ (hrP n hPab) _ (hrQ n hQab) rfl
  order_pres := by
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Set.mem_iUnion] at hab hab'
    obtain ⟨P, hP, hPab⟩ := hab
    obtain ⟨Q, hQ, hQab⟩ := hab'
    obtain ⟨r, hr, hrP, hrQ⟩ := genericFilter_directed hP hQ
    exact (r.seq n).toPartialIso.order_pres _ (hrP n hPab) _ (hrQ n hQab) h

/-- The `n`-th partial automorphism is total: every `a : ℚ` is in its domain. -/
lemma genericPartialIso_total (n : ℕ) : (genericPartialIso n).toPartialInj.Total := by
  intro a
  obtain ⟨p, hp, hpa⟩ := genericFilter_meets_inDomain n a
  obtain ⟨b, hb⟩ := hpa
  exact ⟨b, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hb⟩⟩⟩

/-- The inverse of the `n`-th partial automorphism is also total. -/
lemma genericPartialIso_symm_total (n : ℕ) :
    (genericPartialIso n).toPartialInj.symm.Total := by
  intro b
  obtain ⟨p, hp, hpb⟩ := genericFilter_meets_inRange n b
  obtain ⟨a, ha⟩ := hpb
  exact ⟨a, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ha⟩⟩⟩

/-- The `n`-th generic automorphism of `ℚ`. -/
noncomputable def genericAut (n : ℕ) : ℚ ≃o ℚ :=
  (genericPartialIso n).toIso (genericPartialIso_total n) (genericPartialIso_symm_total n)

/-- Key evaluation lemma: if a condition `p` in the filter maps `a` to `b` at index `n`,
    then `genericAut n a = b`. -/
lemma genericAut_spec (n : ℕ) (p : KnightCondition) (hp : p ∈ genericFilter)
    (a b : ℚ) (h : (a, b) ∈ (p.seq n).graph) :
    genericAut n a = b := by
  have hmem : (a, b) ∈ (genericPartialIso n).graph :=
    Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, h⟩⟩
  simp only [genericAut, PartialIso.toIso]
  change Classical.choose (genericPartialIso_total n a) = b
  exact (genericPartialIso n).functional
    ⟨a, Classical.choose (genericPartialIso_total n a)⟩
    (Classical.choose_spec (genericPartialIso_total n a))
    ⟨a, b⟩ hmem rfl

/-- There exists `r ∈ genericFilter` with `r ≤ p` and `a ∈ (r.seq n).dom` for every index `n`
    appearing in word `w`. -/
lemma exists_extension_with_domain (w : Word) (p : KnightCondition) (hp : p ∈ genericFilter)
    (a : ℚ) :
    ∃ r ∈ genericFilter, r ≤ p ∧ ∀ (n : ℕ), (∃ bl, (n, bl) ∈ w) → a ∈ (r.seq n).dom := by
  induction w generalizing p with
  | nil =>
    exact ⟨p, hp, le_refl _, fun _ ⟨_, h⟩ => by simp at h⟩
  | cons l w' ih =>
    obtain ⟨n, bl⟩ := l
    obtain ⟨q, hq_filter, hq_dom⟩ := genericFilter_meets_inDomain n a
    obtain ⟨r₁, hr₁_filter, hr₁p, hr₁q⟩ := genericFilter_directed hp hq_filter
    have hr₁_dom : r₁ ∈ KnightCondition.inDomain n a :=
      KnightCondition.inDomain_open hq_dom hr₁q
    obtain ⟨r, hr_filter, hr_r₁, hr_dom⟩ := ih r₁ hr₁_filter
    refine ⟨r, hr_filter, le_trans hr_r₁ hr₁p, fun n' hn' => ?_⟩
    obtain ⟨bl', hn'⟩ := hn'
    simp only [List.mem_cons] at hn'
    rcases hn' with h | h
    · have : n' = n := (Prod.mk.inj h).1
      subst this
      exact KnightCondition.inDomain_open hr₁_dom hr_r₁
    · exact hr_dom n' ⟨bl', h⟩

end GenericAut
