/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.ModelIso
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# Forcing Conditions for Knight Model Isomorphisms

This file defines `ModelIsoCondition`, the forcing conditions used to generically construct a
knight isomorphism between two knight models via a back-and-forth argument.

A **condition** is a **finite** `PartialKnightIso`: a finite set of pairs `(a, b)` forming
a partial order-isomorphism compatible with the blueprint action. Conditions are ordered by
extension: `p ≤ q` means `p` extends `q` (i.e. `q.graph ⊆ p.graph`), so smaller conditions
contain more information.

The file's main purpose is to collect the lemmas used in `DenseSets.lean` to show that
`inDomain` and `inRange` are dense: the key results are `canExtend_domain` and `canExtend_range`,
which say that any fresh domain or range element can be added to any condition. These are proved
via a three-case argument on the structure of the existing domain.

## Main definitions

* `ModelIsoCondition α β Ω`: a finite `PartialKnightIso α β Ω`
* `ModelIsoCondition.dom`, `ModelIsoCondition.ran`: the domain and range sets
* `ModelIsoCondition.CanExtend p a b`: predicate asserting that `(a, b)` can be added to `p`
* `ModelIsoCondition.symm`: swap domain and range to get a `β → α` condition

## Main results

* `canExtend_domain`: every `a ∉ p.dom` can be added to any condition `p`
* `canExtend_range`: every `b ∉ p.ran` can be added to any condition `p`

## Tags

forcing, condition, partial isomorphism, back-and-forth, knight model
-/

@[ext]
structure ModelIsoCondition (α β Ω : Type 0) [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] extends PartialKnightIso α β Ω where
  finite : graph.Finite

namespace ModelIsoCondition

variable {α β Ω : Type 0} [Blueprint Ω] [KnightModel α Ω] [KnightModel β Ω]

/-! ## Domain and range -/

/-- The domain: the set of first coordinates in the graph. -/
def dom (p : ModelIsoCondition α β Ω) : Set α :=
  p.toPartialIso.toPartialInj.dom

/-- The range: the set of second coordinates in the graph. -/
def ran (p : ModelIsoCondition α β Ω) : Set β :=
  p.toPartialIso.toPartialInj.ran

/-- `a` is in the domain iff there exists a paired `b`. -/
lemma mem_dom_iff {p : ModelIsoCondition α β Ω} {a : α} :
    a ∈ p.dom ↔ ∃ b, (a, b) ∈ p.graph := by
  rfl

/-- `b` is in the range iff there exists a paired `a`. -/
lemma mem_ran_iff {p : ModelIsoCondition α β Ω} {b : β} :
    b ∈ p.ran ↔ ∃ a, (a, b) ∈ p.graph := by
  rfl

/-- The domain of a finite condition is finite. -/
lemma finite_dom (p : ModelIsoCondition α β Ω) : p.dom.Finite :=
  (p.finite.image Prod.fst).subset fun _ ⟨b, hb⟩ => ⟨(_, b), hb, rfl⟩

/-- The range of a finite condition is finite. -/
lemma finite_ran (p : ModelIsoCondition α β Ω) : p.ran.Finite :=
  (p.finite.image Prod.snd).subset fun _ ⟨a, ha⟩ => ⟨(a, _), ha, rfl⟩

/-! ## Finiteness and maximal-element lemmas -/

/-- If the domain is empty then the graph is empty. -/
lemma graph_eq_empty_of_dom_eq_empty {p : ModelIsoCondition α β Ω} (hdom : p.dom = ∅) :
    p.graph = ∅ := by
  ext ⟨a, b⟩; constructor
  · intro h; have ha : a ∈ p.dom := ⟨b, h⟩; simp [hdom] at ha
  · intro h; simp at h

/-- A nonempty finite domain has a maximum element. -/
lemma exists_max_dom (p : ModelIsoCondition α β Ω) (hdom : p.dom.Nonempty) :
    ∃ c, c ∈ p.dom ∧ ∀ x, x ∈ p.dom → x ≤ c := by
  classical
  let s : Finset α := (p.finite_dom).toFinset
  have hsne : s.Nonempty := by
    rcases hdom with ⟨x, hx⟩
    exact ⟨x, by simpa [s, Set.Finite.mem_toFinset] using hx⟩
  refine ⟨s.max' hsne, ?_, ?_⟩
  · simpa [s, Set.Finite.mem_toFinset] using Finset.max'_mem s hsne
  · intro x hx
    have hx' : x ∈ s := by simpa [s, Set.Finite.mem_toFinset] using hx
    exact Finset.le_max' s x hx'

/-! ## Empty condition and ordering -/

/-- The empty condition: empty graph, trivially finite. -/
def empty : ModelIsoCondition α β Ω where
  toPartialKnightIso := PartialKnightIso.empty
  finite := by
    simp [PartialKnightIso.empty, PartialIso.empty, PartialInj.empty]

instance : Inhabited (ModelIsoCondition α β Ω) := ⟨empty⟩

instance : EmptyCollection (ModelIsoCondition α β Ω) := ⟨empty⟩

/-- The forcing order: `p ≤ q` means `p` is a stronger condition (its graph contains `q`'s). -/
instance : Preorder (ModelIsoCondition α β Ω) where
  le p q := q.graph ⊆ p.graph
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ hpq hqr := Set.Subset.trans hqr hpq

/-! ## Extension -/

/-- A condition obtained by adding exactly one new pair `(a, b)` to `p`. -/
structure Extension (p : ModelIsoCondition α β Ω) (a : α) (b : β)
    extends ModelIsoCondition α β Ω where
  spec : graph = p.graph ∪ {⟨a, b⟩}

instance {p : ModelIsoCondition α β Ω} {a : α} {b : β} :
    CoeOut (p.Extension a b) (ModelIsoCondition α β Ω) where
  coe := Extension.toModelIsoCondition

/-- Predicate asserting that adding the pair `(a, b)` to `p` yields a valid condition.
Wraps `PartialKnightIso.CanExtend`, which checks order-compatibility and fn-compatibility. -/
structure CanExtend (p : ModelIsoCondition α β Ω) (a : α) (b : β) : Prop where
  toCanExtendPKI : p.toPartialKnightIso.CanExtend a b

/-- Build the extended condition from a `CanExtend` proof, inheriting all invariants. -/
def CanExtend.toExtension {p : ModelIsoCondition α β Ω} {a : α} {b : β}
    (h : p.CanExtend a b) : p.Extension a b :=
  let gExt := h.toCanExtendPKI.toExtension
  { toPartialKnightIso := gExt.toPartialKnightIso
    finite := gExt.spec ▸ p.finite.union (Set.finite_singleton _)
    spec := gExt.spec }

/-- A `CanExtend` proof yields a condition extending `p` that contains the pair `(a, b)`. -/
lemma CanExtend.exists_extension {p : ModelIsoCondition α β Ω} {a : α} {b : β}
    (h : p.CanExtend a b) :
    ∃ q : ModelIsoCondition α β Ω, q ≤ p ∧ ⟨a, b⟩ ∈ q.graph := by
  refine ⟨h.toExtension, fun _ hp => ?_, ?_⟩ <;> rw [h.toExtension.spec]
  · exact Set.mem_union_left _ hp
  · exact Set.mem_union_right _ (Set.mem_singleton _)

/-- If `p.CanExtend a b`, then `a` is not already in the domain of `p`. -/
lemma not_mem_dom_of_canExtend {p : ModelIsoCondition α β Ω} {a : α} {b : β}
    (h : p.CanExtend a b) : a ∉ p.dom :=
  h.toCanExtendPKI.toCanExtendIso.toCanExtend.freshDom

/-- If `p.CanExtend a b`, then `b` is not already in the range of `p`. -/
lemma not_mem_ran_of_canExtend {p : ModelIsoCondition α β Ω} {a : α} {b : β}
    (h : p.CanExtend a b) : b ∉ p.ran :=
  h.toCanExtendPKI.toCanExtendIso.toCanExtend.freshRan

/-! ## Domain extension: the three-case argument

The main goal is `canExtend_domain`: for any `a ∉ p.dom` we can extend `p` with some `(a, b)`.
The proof splits into three cases based on the existing domain:
1. The domain is empty — any `b` works.
2. `a ≤ c` where `c` is the domain maximum — pair `a` with `fn n d` where `a = fn n c`.
3. `c ≤ a` — choose a fresh range element strictly above `d` using `KnightModel.extend`.

The key helper `exists_index_of_mem_graph_of_max` underpins cases 2 and 3: every existing
graph pair is a blueprint image of the maximum-domain pair.
-/

/-- When the domain is empty, any fresh `a` can be extended: pair it with an arbitrary `b`. -/
lemma canExtend_domain_case_empty [Nonempty β]
    (p : ModelIsoCondition α β Ω) (a : α) (hdom : p.dom = ∅) (ha : a ∉ p.dom) :
    ∃ b : β, p.CanExtend a b := by
  classical
  have hgraph : p.graph = ∅ := graph_eq_empty_of_dom_eq_empty hdom
  refine ⟨Classical.choice ‹Nonempty β›, { toCanExtendPKI := {
    toCanExtendIso := {
      freshDom := ha
      freshRan := fun hbRan => by
        obtain ⟨_, h⟩ := (mem_ran_iff (p := p)).mp hbRan; simp [hgraph] at h
      orderCompat := fun q hq => by simp [hgraph] at hq }
    fnCompatPre := fun _ q hq => by simp [hgraph] at hq
    fnCompatPost := fun _ q hq => by simp [hgraph] at hq } }⟩


/-- Blueprint application is injective in the index: `fn m a = fn n a ↔ m = n`. -/
lemma fn_eq_iff_index_eq (a : α) {m n : Ω} :
    KnightModel.fn m a = KnightModel.fn n a ↔ m = n :=
  ⟨fun h => le_antisymm ((KnightModel.blueprint_ord n m a).mp (le_of_eq h))
    ((KnightModel.blueprint_ord m n a).mp (le_of_eq h.symm)), fun h => by simp [h]⟩

/-- Every graph pair `(x, y)` is a blueprint image of the maximum-domain pair `(c, d)`:
there exists `n` with `x = fn n c` and `y = fn n d`. -/
lemma exists_index_of_mem_graph_of_max
    {p : ModelIsoCondition α β Ω} {c : α} {d : β}
    (hcMax : ∀ x, x ∈ p.dom → x ≤ c) (hcd : (c, d) ∈ p.graph)
    {x : α} {y : β} (hxy : (x, y) ∈ p.graph) :
    ∃ n : Ω, x = KnightModel.fn n c ∧ y = KnightModel.fn n d := by
  obtain ⟨n, hn⟩ := KnightModel.capture x c (hcMax x ((mem_dom_iff (p := p)).2 ⟨y, hxy⟩))
  exact ⟨n, hn.symm, (p.fn_compat n (c, d) hcd (x, y) hxy).1 hn.symm⟩

-- Both fn-compatibility conditions for a new pair `(a, b)` reduce to the same index
-- equation once `q` and `(a, b)` are expressed as blueprint images of a common base.
-- blueprint_comp : fn m (fn n a) = fn (m * n) a  (forward direction simplifies nested fn)
private lemma fn_compat_of_fn_eq {q : α × β} {a : α} {b : β} {c : α} {d : β} {n n₀ : Ω}
    (hq1 : q.1 = KnightModel.fn n c) (hq2 : q.2 = KnightModel.fn n d)
    (ha : a = KnightModel.fn n₀ c) (hb : b = KnightModel.fn n₀ d) (m : Ω) :
    (a = KnightModel.fn m q.1 ↔ b = KnightModel.fn m q.2) ∧
    (q.1 = KnightModel.fn m a ↔ q.2 = KnightModel.fn m b) := by
  simp only [hq1, hq2, ha, hb, KnightModel.blueprint_comp]
  exact ⟨(fn_eq_iff_index_eq c).trans (fn_eq_iff_index_eq d).symm,
         (fn_eq_iff_index_eq c).trans (fn_eq_iff_index_eq d).symm⟩

-- Order-compatibility also reduces to a single index inequality via `blueprint_ord`.
private lemma order_compat_of_fn_eq {q : α × β} {a : α} {b : β} {c : α} {d : β} {n n₀ : Ω}
    (hq1 : q.1 = KnightModel.fn n c) (hq2 : q.2 = KnightModel.fn n d)
    (ha : a = KnightModel.fn n₀ c) (hb : b = KnightModel.fn n₀ d) :
    q.1 ≤ a ↔ q.2 ≤ b := by
  simp only [hq1, hq2, ha, hb]
  exact (KnightModel.blueprint_ord n₀ n c).trans (KnightModel.blueprint_ord n₀ n d).symm

/-- When `a ≤ c` (the domain maximum), extend `p` by pairing `a` with `fn n d`
where `n` is the unique index with `a = fn n c`. -/
lemma canExtend_domain_case_le_max
    (p : ModelIsoCondition α β Ω)
    (a c : α) (d : β)
    (_hcDom : c ∈ p.dom)
    (hcMax : ∀ x, x ∈ p.dom → x ≤ c)
    (hcd : (c, d) ∈ p.graph)
    (hac : a ≤ c)
    (ha : a ∉ p.dom) :
    ∃ b : β, p.CanExtend a b := by
  obtain ⟨n0, hn0⟩ := KnightModel.capture a c hac
  let b : β := KnightModel.fn n0 d
  have hna : a = KnightModel.fn n0 c := hn0.symm
  have hnb : b = KnightModel.fn n0 d := rfl
  refine ⟨b, { toCanExtendPKI := {
    toCanExtendIso := {
      freshDom := ha
      freshRan := fun hbRan => by
        obtain ⟨x, hxb⟩ := (mem_ran_iff (p := p)).mp hbRan
        obtain ⟨n, hnx, hnb'⟩ := exists_index_of_mem_graph_of_max hcMax hcd hxb
        have hneq : n = n0 := (fn_eq_iff_index_eq d).1 (hnb'.symm.trans hnb)
        exact ha ((mem_dom_iff (p := p)).2 ⟨b,
          (by simp only [hnx, hneq, ← hna] : x = a) ▸ hxb⟩)
      orderCompat := fun q hq => by
        obtain ⟨n, hnq1, hnq2⟩ := exists_index_of_mem_graph_of_max hcMax hcd hq
        exact order_compat_of_fn_eq hnq1 hnq2 hna hnb }
    fnCompatPre := fun m q hq => by
      obtain ⟨n, hnq1, hnq2⟩ := exists_index_of_mem_graph_of_max hcMax hcd hq
      exact (fn_compat_of_fn_eq hnq1 hnq2 hna hnb m).1
    fnCompatPost := fun m q hq => by
      obtain ⟨n, hnq1, hnq2⟩ := exists_index_of_mem_graph_of_max hcMax hcd hq
      exact (fn_compat_of_fn_eq hnq1 hnq2 hna hnb m).2 } }⟩

/-- When `c ≤ a` (above the domain maximum), extend `p` by choosing a fresh range element
strictly above `d` using `KnightModel.extend`, then pair `a` with it. -/
lemma canExtend_domain_case_ge_max
    (p : ModelIsoCondition α β Ω)
    (a c : α) (d : β)
    (hcDom : c ∈ p.dom)
    (hcMax : ∀ x, x ∈ p.dom → x ≤ c)
    (hcd : (c, d) ∈ p.graph)
    (hca : c ≤ a)
    (ha : a ∉ p.dom) :
    ∃ b : β, p.CanExtend a b := by
  obtain ⟨n0, hn0⟩ := KnightModel.capture c a hca
  obtain ⟨u, hdu⟩ := exists_gt d
  obtain ⟨b, hdb, _, hnb⟩ := KnightModel.extend n0 d u hdu
  refine ⟨b, { toCanExtendPKI := {
    toCanExtendIso := {
      freshDom := ha
      freshRan := fun hbRan => by
        obtain ⟨x, hxb⟩ := (mem_ran_iff (p := p)).mp hbRan
        have hxc : x ≤ c := hcMax x ((mem_dom_iff (p := p)).2 ⟨b, hxb⟩)
        have hEqbd : b = d := le_antisymm (p.order_pres (x, b) hxb (c, d) hcd hxc) hdb
        have hfix : KnightModel.fn n0 b = b := by simpa [hEqbd] using hnb
        have hn01 : n0 = (1 : Ω) := le_antisymm (Blueprint.one_le n0)
          ((KnightModel.blueprint_ord n0 1 b).1 (by simp [KnightModel.fn_one_eq_id b, hfix]))
        have hac : a = c := by
          have h := hn0; simp only [hn01, KnightModel.fn_one_eq_id] at h; exact h
        exact ha (hac ▸ hcDom)
      orderCompat := fun q hq => by
        have hqc : q.1 ≤ c := hcMax q.1 ((mem_dom_iff (p := p)).2 ⟨q.2, hq⟩)
        exact ⟨fun _ => le_trans (p.order_pres q hq (c, d) hcd hqc) hdb,
               fun _ => le_trans hqc hca⟩ }
    fnCompatPre := fun m q hq => by
      obtain ⟨n, hnq1, hnq2⟩ := exists_index_of_mem_graph_of_max hcMax hcd hq
      have hq1a : q.1 = KnightModel.fn (n * n0) a := by
        simp only [hnq1, ← hn0, KnightModel.blueprint_comp]
      have hq2b : q.2 = KnightModel.fn (n * n0) b := by
        simp only [hnq2, ← hnb, KnightModel.blueprint_comp]
      exact (fn_compat_of_fn_eq hq1a hq2b
        (KnightModel.fn_one_eq_id a).symm (KnightModel.fn_one_eq_id b).symm m).1
    fnCompatPost := fun m q hq => by
      obtain ⟨n, hnq1, hnq2⟩ := exists_index_of_mem_graph_of_max hcMax hcd hq
      have hq1a : q.1 = KnightModel.fn (n * n0) a := by
        simp only [hnq1, ← hn0, KnightModel.blueprint_comp]
      have hq2b : q.2 = KnightModel.fn (n * n0) b := by
        simp only [hnq2, ← hnb, KnightModel.blueprint_comp]
      exact (fn_compat_of_fn_eq hq1a hq2b
        (KnightModel.fn_one_eq_id a).symm (KnightModel.fn_one_eq_id b).symm m).2 } }⟩


/-! ## Symmetry -/

/-- Symmetric of a condition: swap domain and range to get a `β → α` condition. -/
def symm (p : ModelIsoCondition α β Ω) : ModelIsoCondition β α Ω where
  toPartialKnightIso := p.toPartialKnightIso.symm
  finite := by
    change Set.Finite {q : β × α | (q.2, q.1) ∈ p.graph}
    have : {q : β × α | (q.2, q.1) ∈ p.graph} = Prod.swap ⁻¹' p.graph := by ext; simp [Prod.swap]
    rw [this]
    exact p.finite.preimage Prod.swap_injective.injOn

/-- Membership in the symmetric condition: `(b, a) ∈ p.symm.graph ↔ (a, b) ∈ p.graph`. -/
@[simp]
lemma mem_symm_graph {p : ModelIsoCondition α β Ω} {a : α} {b : β} :
    (b, a) ∈ p.symm.graph ↔ (a, b) ∈ p.graph := by
  simp [symm, PartialKnightIso.symm, PartialIso.symm, PartialInj.symm]

/-- Symmetry is an involution on conditions. -/
@[simp]
lemma symm_symm (p : ModelIsoCondition α β Ω) : p.symm.symm = p := by
  ext x
  simp [symm, PartialKnightIso.symm, PartialIso.symm, PartialInj.symm]

/-- The extension order respects symmetry: `p.symm ≤ q.symm ↔ p ≤ q`. -/
lemma symm_le_symm_iff {p q : ModelIsoCondition α β Ω} : p.symm ≤ q.symm ↔ p ≤ q :=
  ⟨fun h _ hxy => mem_symm_graph.mp (h (mem_symm_graph.mpr hxy)),
   fun h _ hba => mem_symm_graph.mpr (h (mem_symm_graph.mp hba))⟩

/-- The domain of `p.symm` equals the range of `p`. -/
lemma mem_dom_symm_iff_mem_ran {p : ModelIsoCondition α β Ω} {b : β} :
    b ∈ p.symm.dom ↔ b ∈ p.ran := by
  simp only [mem_dom_iff, mem_ran_iff, mem_symm_graph]

/-- The range of `p.symm` equals the domain of `p`. -/
lemma mem_ran_symm_iff_mem_dom {p : ModelIsoCondition α β Ω} {a : α} :
    a ∈ p.symm.ran ↔ a ∈ p.dom := by
  simp only [mem_ran_iff, mem_dom_iff, mem_symm_graph]

/-- If `p` can be extended by `(a, b)`, then `p.symm` can be extended by `(b, a)`. -/
lemma canExtend_symm {p : ModelIsoCondition α β Ω} {a : α} {b : β}
    (h : p.CanExtend a b) : p.symm.CanExtend b a :=
  { toCanExtendPKI :=
    { toCanExtendIso :=
      { freshDom := mt mem_dom_symm_iff_mem_ran.mp (not_mem_ran_of_canExtend h)
        freshRan := mt mem_ran_symm_iff_mem_dom.mp (not_mem_dom_of_canExtend h)
        orderCompat := fun q hq =>
          (h.toCanExtendPKI.toCanExtendIso.orderCompat (q.2, q.1) (mem_symm_graph.mp hq)).symm }
      fnCompatPre := fun n q hq =>
        (h.toCanExtendPKI.fnCompatPre n (q.2, q.1) (mem_symm_graph.mp hq)).symm
      fnCompatPost := fun n q hq =>
        (h.toCanExtendPKI.fnCompatPost n (q.2, q.1) (mem_symm_graph.mp hq)).symm } }

/-- Extension capability is symmetric: `p.symm.CanExtend b a ↔ p.CanExtend a b`. -/
lemma canExtend_symm_iff {p : ModelIsoCondition α β Ω} {a : α} {b : β} :
    p.symm.CanExtend b a ↔ p.CanExtend a b :=
  ⟨fun h => by simpa using canExtend_symm (p := p.symm) h, canExtend_symm⟩

/-- Reduce range-extension to domain-extension on the symmetric condition:
if every fresh domain element can be added on `p.symm`, then every fresh range element
can be added on `p`. -/
theorem canExtend_range_of_domain_on_symm
    (hDomInv : ∀ q : ModelIsoCondition β α Ω, ∀ b : β,
      b ∉ q.dom → ∃ a : α, q.CanExtend b a) :
    ∀ p : ModelIsoCondition α β Ω, ∀ b : β,
      b ∉ p.ran → ∃ a : α, p.CanExtend a b := fun p b hbFresh => by
  obtain ⟨a, ha⟩ := hDomInv p.symm b (mt mem_dom_symm_iff_mem_ran.mp hbFresh)
  exact ⟨a, canExtend_symm_iff.mp ha⟩

/-! ## Main density theorems -/

/-- Every fresh domain element `a ∉ p.dom` can be added to any condition `p`.
This is the key density result used in `DenseSets.lean` for `inDomain`. -/
theorem canExtend_domain [Nonempty β] :
    ∀ p : ModelIsoCondition α β Ω, ∀ a : α,
      a ∉ p.dom → ∃ b : β, p.CanExtend a b := by
  intro p a hFresh
  by_cases hEmpty : p.dom = ∅
  · exact canExtend_domain_case_empty p a hEmpty hFresh
  · have hDomNe : p.dom.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨c, hcDom, hcMax⟩ := p.exists_max_dom hDomNe
    obtain ⟨d, hcd⟩ := (mem_dom_iff (p := p)).mp hcDom
    by_cases hac : a ≤ c
    · exact canExtend_domain_case_le_max p a c d hcDom hcMax hcd hac hFresh
    · exact canExtend_domain_case_ge_max p a c d hcDom hcMax hcd (le_of_not_ge hac) hFresh

/-- Every fresh range element `b ∉ p.ran` can be added to any condition `p`.
This is the key density result used in `DenseSets.lean` for `inRange`. -/
theorem canExtend_range [Nonempty α] :
    ∀ p : ModelIsoCondition α β Ω, ∀ b : β,
      b ∉ p.ran → ∃ a : α, p.CanExtend a b :=
  canExtend_range_of_domain_on_symm fun q b hb => canExtend_domain q b hb

end ModelIsoCondition
