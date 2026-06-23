/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Condition
import Mathlib

/-!
# Dense Sets for the Model Forcing

This file proves that the two key families of sets are **dense** in the forcing order on
`ModelIsoCondition α β Ω`. Density is required by the Rasiowa–Sikorski theorem to ensure
the generic filter meets every relevant dense set.

The two families are:
- `inDomain a`: conditions whose domain contains `a`
- `inRange b`: conditions whose range contains `b`

Both are shown to be open (downward closed in the extension order) and dense: every condition
can be extended to one in the set.

## Main results

* `ModelIsoCondition.inDomain_open`: `inDomain a` is open
* `ModelIsoCondition.inDomain_dense`: `inDomain a` is dense
* `ModelIsoCondition.inRange_open`: `inRange b` is open
* `ModelIsoCondition.inRange_dense`: `inRange b` is dense

## Tags

dense sets, forcing, back-and-forth, knight model, generic filter
-/

namespace ModelIsoCondition

variable {α β Ω : Type 0} [Blueprint Ω] [KnightModel α Ω] [KnightModel β Ω]

def inDomain (a : α) : Set (ModelIsoCondition α β Ω) :=
  {p | ∃ b, (a, b) ∈ p.graph}

lemma inDomain_open {a : α} {p q : ModelIsoCondition α β Ω}
    (hp : p ∈ inDomain a) (hpq : q ≤ p) : q ∈ inDomain a := by
  obtain ⟨b, hb⟩ := hp
  exact ⟨b, hpq hb⟩

def inRange (b : β) : Set (ModelIsoCondition α β Ω) :=
  {p | ∃ a, (a, b) ∈ p.graph}

private lemma inDomain_of_canExtend {a : α} {p : ModelIsoCondition α β Ω}
    (hcan : ∃ b, p.CanExtend a b) :
    ∃ q ≤ p, q ∈ inDomain a := by
  obtain ⟨b, hb⟩ := hcan
  obtain ⟨q, hqp, hmem⟩ := hb.exists_extension
  exact ⟨q, hqp, ⟨b, hmem⟩⟩

private lemma inRange_of_canExtend {b : β} {p : ModelIsoCondition α β Ω}
    (hcan : ∃ a, p.CanExtend a b) :
    ∃ q ≤ p, q ∈ inRange b := by
  obtain ⟨a, ha⟩ := hcan
  obtain ⟨q, hqp, hmem⟩ := ha.exists_extension
  exact ⟨q, hqp, ⟨a, hmem⟩⟩

lemma mem_inRange_iff_symm_mem_inDomain {b : β} {p : ModelIsoCondition α β Ω} :
    p ∈ inRange b ↔ p.symm ∈ inDomain b := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      simpa [ModelIsoCondition.symm, PartialKnightIso.symm, PartialIso.symm, PartialInj.symm]
        using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      simpa [ModelIsoCondition.symm, PartialKnightIso.symm, PartialIso.symm, PartialInj.symm]
        using ha⟩

lemma inRange_open {b : β} {p q : ModelIsoCondition α β Ω}
    (hp : p ∈ inRange b) (hpq : q ≤ p) : q ∈ inRange b := by
  rw [mem_inRange_iff_symm_mem_inDomain] at hp ⊢
  exact inDomain_open hp (symm_le_symm_iff.mpr hpq)

lemma inDomain_dense [Nonempty β] (a : α) (p : ModelIsoCondition α β Ω) :
    ∃ q ≤ p, q ∈ inDomain a := by
  by_cases ha : ∃ b, (a, b) ∈ p.graph
  · exact ⟨p, le_rfl, ha⟩
  · have hcan : ∃ b, p.CanExtend a b := by
      have hFresh : a ∉ p.dom := by
        intro haDom
        exact ha ((mem_dom_iff (p := p)).mp haDom)
      exact canExtend_domain (α := α) (β := β) (Ω := Ω) p a hFresh
    exact inDomain_of_canExtend hcan

lemma inRange_dense [Nonempty α] (b : β) (p : ModelIsoCondition α β Ω) :
    ∃ q ≤ p, q ∈ inRange b := by
  by_cases hb : ∃ a, (a, b) ∈ p.graph
  · exact ⟨p, le_rfl, hb⟩
  · have hcan : ∃ a, p.CanExtend a b := by
      have hFresh : b ∉ p.ran := by
        intro hbRan
        exact hb ((mem_ran_iff (p := p)).mp hbRan)
      exact canExtend_range (α := α) (β := β) (Ω := Ω) p b hFresh
    exact inRange_of_canExtend hcan

lemma inRange_dense_via_inv [Nonempty α]
    (b : β) (p : ModelIsoCondition α β Ω) :
    ∃ q ≤ p, q ∈ inRange b := by
  obtain ⟨q, hq, hqmem⟩ := inDomain_dense (α := β) (β := α) (Ω := Ω) b p.symm
  refine ⟨q.symm, ?_, ?_⟩
  · exact symm_symm p ▸ symm_le_symm_iff.mpr hq
  · exact mem_inRange_iff_symm_mem_inDomain.mpr (symm_symm q ▸ hqmem)

end ModelIsoCondition
