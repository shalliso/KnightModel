/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Order.Hom.Basic

/-!
# Partial Injections and Isomorphisms

This file defines types of partial maps. Rather than extending existing API for partial maps
we define them from scratch, which turned out to be more pleasant.

## Main definitions

* `PartialInj α β`: A partial injection — a set of `(α × β)` pairs that is functional
  and injective.
* `PartialIso α β`: A `PartialInj` that additionally preserves a linear order.
* `FixingPartialAut α`: A `PartialIso α α` satisfying the *fixing* property: if `b` is a
  fixed point and `a ≤ b`, then `a` is also a fixed point. Such automorphisms are relevant
  to the construction of Knight models

Each structure comes with:
* `symm`: swap domain and range (type-swapping)
* `Extension`: represents extending a graph extended by a new pair, can be coerced to the new graph
* `CanExtend`: predicate collecting sufficient conditions for when a pair can be added to a graph
* `CanExtend.toExtension`: constructs the `Extension` from a `CanExtend` proof

The `Extension` is useful for recursion and induction as it remembers what pair was added to
the graph last.

## Tags

partial injection, partial isomorphism, fixing partial automorphism, forcing condition
-/

/-! ## Partial Injections -/

@[ext]
structure PartialInj (α β : Type 0) where
  graph : Set (α × β)
  functional : ∀ p ∈ graph, ∀ q ∈ graph, p.1 = q.1 → p.2 = q.2
  injective : ∀ p ∈ graph, ∀ q ∈ graph, p.2 = q.2 → p.1 = q.1

namespace PartialInj

variable {α β γ}

def dom (f : PartialInj α β) : Set α := {a : α | ∃ b : β, (a, b) ∈ f.graph}

def ran (f : PartialInj α β) : Set β := {b : β | ∃ a : α, (a, b) ∈ f.graph}

open Classical in
noncomputable def apply? (f : PartialInj α β) (a : α) : Option β :=
  if h : ∃ b, (a, b) ∈ f.graph then some (choose h) else none

lemma apply?_of_mem {f : PartialInj α β} {a : α} {b : β} (h : (a, b) ∈ f.graph) :
    f.apply? a = some b := by
  have hex : ∃ b, (a, b) ∈ f.graph := ⟨b, h⟩
  unfold apply?
  rw [dif_pos hex]
  exact congr_arg some (f.functional _ (Classical.choose_spec hex) _ h rfl)

lemma apply?_eq_none {f : PartialInj α β} {a : α} (h : a ∉ f.dom) :
    f.apply? a = none :=
  dif_neg h

lemma mem_graph_of_apply? {f : PartialInj α β} {a : α} {b : β}
    (h : f.apply? a = some b) : (a, b) ∈ f.graph := by
  unfold apply? at h
  split_ifs at h with hex
  exact Option.some.inj h ▸ Classical.choose_spec hex

lemma apply?_of_graph_subset {f g : PartialInj α β}
    (hsub : f.graph ⊆ g.graph) {a : α} {b : β}
    (h : f.apply? a = some b) : g.apply? a = some b :=
  apply?_of_mem (hsub (mem_graph_of_apply? h))

def comp (g : PartialInj β γ) (f : PartialInj α β) : PartialInj α γ where
  graph := {p | ∃ b, (p.1, b) ∈ f.graph ∧ (b, p.2) ∈ g.graph}
  functional := fun p hp q hq hpq => by
    obtain ⟨b₁, hf₁, hg₁⟩ := hp
    obtain ⟨b₂, hf₂, hg₂⟩ := hq
    have : b₁ = b₂ := f.functional (p.1, b₁) hf₁ (q.1, b₂) hf₂ (by simp [hpq])
    exact g.functional (b₁, p.2) hg₁ (b₂, q.2) hg₂ (by simp [this])
  injective := fun p hp q hq hpq => by
    obtain ⟨b₁, hf₁, hg₁⟩ := hp
    obtain ⟨b₂, hf₂, hg₂⟩ := hq
    have : b₁ = b₂ := g.injective (b₁, p.2) hg₁ (b₂, q.2) hg₂ (by simp [hpq])
    exact f.injective (p.1, b₁) hf₁ (q.1, b₂) hf₂ (by simp [this])

def symm (f : PartialInj α β) : PartialInj β α where
  graph := {p | (p.2, p.1) ∈ f.graph}
  functional := fun p hp q hq => f.injective (p.2, p.1) hp (q.2, q.1) hq
  injective := fun p hp q hq => f.functional (p.2, p.1) hp (q.2, q.1) hq

lemma symm_graph_subset {f g : PartialInj α β}
    (hsub : f.graph ⊆ g.graph) : f.symm.graph ⊆ g.symm.graph :=
  fun _ hp => hsub hp

def Total (f : PartialInj α β) : Prop :=
  ∀ a, ∃ b, (a, b) ∈ f.graph

noncomputable def toFun (f : PartialInj α β) (h : f.Total) : α → β :=
  fun a => Classical.choose (h a)

def empty : PartialInj α β where
  graph := ∅
  functional := by simp
  injective := by simp

instance : Inhabited (PartialInj α β) := ⟨empty⟩

instance : EmptyCollection (PartialInj α β) := ⟨empty⟩

infixl:90 " ∘ " => comp

instance : InvolutiveInv (PartialInj α α) where
  inv := symm
  inv_inv f := by ext ⟨a, b⟩; simp [symm]

@[simp]
lemma inv_graph (f : PartialInj α α) : (f⁻¹).graph = {p | (p.2, p.1) ∈ f.graph} := rfl

/-- The result of adding one new pair `(a, b)` to the graph of `f`. -/
structure Extension (f : PartialInj α β) (a : α) (b : β) extends PartialInj α β where
  spec : graph = f.graph ∪ {⟨a, b⟩}

instance {f : PartialInj α β} {a : α} {b : β} : CoeOut (f.Extension a b) (PartialInj α β) where
  coe := Extension.toPartialInj

/-- `f.CanExtend a b` holds when `(a, b)` can be added to `f` without violating
functionality or injectivity: `a` must not already be in the domain and `b` must not
already be in the range. -/
structure CanExtend (f : PartialInj α β) (a : α) (b : β) : Prop where
  freshDom : a ∉ f.dom
  freshRan : b ∉ f.ran

/-- Construct the extension of `f` by `(a, b)`, given a `CanExtend` proof. -/
def CanExtend.toExtension {f : PartialInj α β} {a : α} {b : β}
  (h : f.CanExtend a b) : f.Extension a b :=
  {
    graph := f.graph ∪ {(a, b)}
    functional := by
      intro p hp q hq hpq
      cases hp with
      | inl hpf =>
        cases hq with
        | inl hqf =>
          exact f.functional p hpf q hqf hpq
        | inr hqn =>
          obtain rfl := Set.mem_singleton_iff.mp hqn
          have : p = (a, p.2) := Prod.ext hpq rfl
          exact absurd ⟨p.2, this ▸ hpf⟩ h.freshDom
      | inr hpn =>
        cases hq with
        | inl hqf =>
          obtain rfl := Set.mem_singleton_iff.mp hpn
          have : q = (a, q.2) := Prod.ext hpq.symm rfl
          exact absurd ⟨q.2, this ▸ hqf⟩ h.freshDom
        | inr hqn =>
          obtain rfl := Set.mem_singleton_iff.mp hpn
          obtain rfl := Set.mem_singleton_iff.mp hqn
          rfl
    injective := by
      intro p hp q hq hpq
      cases hp with
      | inl hpf =>
        cases hq with
        | inl hqf =>
          exact f.injective p hpf q hqf hpq
        | inr hqn =>
          obtain rfl := Set.mem_singleton_iff.mp hqn
          have : p = (p.1, b) := Prod.ext rfl hpq
          exact absurd ⟨p.1, this ▸ hpf⟩ h.freshRan
      | inr hpn =>
        cases hq with
        | inl hqf =>
          obtain rfl := Set.mem_singleton_iff.mp hpn
          have : q = (q.1, b) := Prod.ext rfl hpq.symm
          exact absurd ⟨q.1, this ▸ hqf⟩ h.freshRan
        | inr hqn =>
          obtain rfl := Set.mem_singleton_iff.mp hpn
          obtain rfl := Set.mem_singleton_iff.mp hqn
          rfl
    spec := rfl
  }
end PartialInj

/-! ## Partial Isomorphisms -/

@[ext]
structure PartialIso (α β : Type 0) [LinearOrder α] [LinearOrder β]
    extends PartialInj α β where
  order_pres : ∀ p ∈ graph, ∀ q ∈ graph, p.1 ≤ q.1 → p.2 ≤ q.2

namespace PartialIso

variable {α β γ} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

instance : Coe (PartialIso α β) (PartialInj α β) where
  coe := PartialIso.toPartialInj

lemma order_pres_iff (f : PartialIso α β) {p q : α × β} (hp : p ∈ f.graph)
    (hq : q ∈ f.graph) : p.1 ≤ q.1 ↔ p.2 ≤ q.2 :=
  ⟨f.order_pres p hp q hq, fun h => by
    by_contra h'
    push Not at h'
    have h₁ : q.2 ≤ p.2 := f.order_pres q hq p hp (le_of_lt h')
    have h₂ : p.2 = q.2 := le_antisymm h h₁
    have h₃ : p.1 = q.1 := f.injective p hp q hq h₂
    exact absurd (h₃ ▸ h') (lt_irrefl q.1)⟩

def comp (g : PartialIso β γ) (f : PartialIso α β) : PartialIso α γ where
  toPartialInj := g.toPartialInj.comp f.toPartialInj
  order_pres := fun p hp q hq hpq => by
    obtain ⟨b₁, hf₁, hg₁⟩ := hp
    obtain ⟨b₂, hf₂, hg₂⟩ := hq
    have : b₁ ≤ b₂ := f.order_pres (p.1, b₁) hf₁ (q.1, b₂) hf₂ hpq
    exact g.order_pres (b₁, p.2) hg₁ (b₂, q.2) hg₂ this

def symm (f : PartialIso α β) : PartialIso β α where
  toPartialInj := f.toPartialInj.symm
  order_pres := fun _ hp _ hq h => (f.order_pres_iff hp hq).mpr h

infixl:90 " ∘ " => comp

instance : InvolutiveInv (PartialIso α α) where
  inv := symm
  inv_inv f := by ext ⟨a, b⟩; simp [symm, PartialInj.symm]

@[simp]
lemma inv_toPartialInj (f : PartialIso α α) : (f⁻¹).toPartialInj = f.toPartialInj.symm := rfl

noncomputable def toIso (f : PartialIso α β) (hf : f.toPartialInj.Total)
    (hf' : f.toPartialInj.symm.Total) : α ≃o β where
  toFun := f.toPartialInj.toFun hf
  invFun := f.toPartialInj.symm.toFun hf'
  left_inv := by
    intro a
    have ⟨b, hab⟩ := hf a
    change Classical.choose (hf' (Classical.choose (hf a))) = a
    have e1 : Classical.choose (hf a) = b :=
      f.functional _ (Classical.choose_spec (hf a)) _ hab rfl
    rw [e1]
    exact f.injective _ (Classical.choose_spec (hf' b)) _ hab rfl
  right_inv := by
    intro b
    have ⟨a, hab⟩ := hf' b
    change Classical.choose (hf (Classical.choose (hf' b))) = b
    have e1 : Classical.choose (hf' b) = a :=
      f.injective _ (Classical.choose_spec (hf' b)) _ hab rfl
    rw [e1]
    exact f.functional _ (Classical.choose_spec (hf a)) _ hab rfl
  map_rel_iff' := by
    intro a₁ a₂
    have ⟨b₁, h₁⟩ := hf a₁
    have ⟨b₂, h₂⟩ := hf a₂
    change (Classical.choose (hf a₁) ≤ Classical.choose (hf a₂)) ↔ (a₁ ≤ a₂)
    have e₁ : Classical.choose (hf a₁) = b₁ :=
      f.functional _ (Classical.choose_spec (hf a₁)) _ h₁ rfl
    have e₂ : Classical.choose (hf a₂) = b₂ :=
      f.functional _ (Classical.choose_spec (hf a₂)) _ h₂ rfl
    rw [e₁, e₂]
    exact (f.order_pres_iff h₁ h₂).symm

def empty : PartialIso α β where
  toPartialInj := PartialInj.empty
  order_pres := by intro _ _ _ h; contradiction

instance : Inhabited (PartialIso α β) := ⟨empty⟩

instance : EmptyCollection (PartialIso α β) := ⟨empty⟩

/-- The result of adding one new pair `(a, b)` to the graph of `f`. -/
structure Extension (f : PartialIso α β) (a : α) (b : β) extends PartialIso α β where
  spec : graph = f.graph ∪ {⟨a, b⟩}

instance {f : PartialIso α β} {a : α} {b : β} : CoeOut (f.Extension a b) (PartialIso α β) where
  coe := Extension.toPartialIso

/-- `f.CanExtend a b` holds when `(a, b)` can be added to `f` while preserving
order-compatibility. Besides freshness (`a ∉ dom f`, `b ∉ ran f`), every existing pair
`(c, d)` must satisfy `c ≤ a ↔ d ≤ b`. -/
structure CanExtend (f : PartialIso α β) (a : α) (b : β) : Prop
      extends f.toPartialInj.CanExtend a b where
    orderCompat : ∀ p ∈ f.graph, (p.1 ≤ a ↔ p.2 ≤ b)

/-- Construct the extension of `f` by `(a, b)`, given a `CanExtend` proof. -/
def CanExtend.toExtension {f : PartialIso α β} {a : α} {b : β}
  (h : f.CanExtend a b) : f.Extension a b :=
  have g_ext := h.toCanExtend.toExtension
  {
    graph := g_ext.graph
    functional := g_ext.functional
    injective := g_ext.injective
    order_pres := by
      intro p hp q hq hpq
      by_cases hpf : p ∈ f.graph <;> by_cases hqf : q ∈ f.graph
      · -- Both p and q in f.graph
        exact f.order_pres p hpf q hqf hpq
      · -- p in f.graph, q not in f.graph (so q = (a,b))
        rw [g_ext.spec, Set.mem_union] at hq
        cases hq with
        | inl hqf' => exact absurd hqf' hqf
        | inr hq => obtain rfl := Set.mem_singleton_iff.mp hq
                    exact (h.orderCompat p hpf).mp hpq
      · -- p not in f.graph (so p = (a,b)), q in f.graph
        rw [g_ext.spec, Set.mem_union] at hp
        cases hp with
        | inl hpf' => exact absurd hpf' hpf
        | inr hp' => obtain rfl := Set.mem_singleton_iff.mp hp'
                     have : a < q.1 := lt_of_le_of_ne hpq fun heq =>
                       h.toCanExtend.freshDom ⟨q.2, heq.symm ▸ hqf⟩
                     have : ¬(q.1 ≤ a) := not_le.mpr this
                     have : ¬(q.2 ≤ b) := (h.orderCompat q hqf).not.mp this
                     exact le_of_lt (not_le.mp this)
      · -- Both p and q not in f.graph (so both = (a,b))
        rw [g_ext.spec, Set.mem_union] at hp hq
        cases hp with
        | inl hpf' => exact absurd hpf' hpf
        | inr hp' => obtain rfl := Set.mem_singleton_iff.mp hp'
                     cases hq with
                     | inl hqf' => exact absurd hqf' hqf
                     | inr hq' => obtain rfl := Set.mem_singleton_iff.mp hq'; rfl
    spec := g_ext.spec
  }

def isFixing (f : PartialIso α α) :=
    ∀ p ∈ f.graph, ∀ q ∈ f.graph, p.1 = p.2 → q.1 ≤ p.1 → q.1 = q.2

def isFinite (f : PartialIso α β) := f.graph.Finite

end PartialIso

/-! ## Fixing Partial Automorphisms -/

@[ext]
structure FixingPartialAut (α : Type 0) [LinearOrder α]
    extends PartialIso α α where
  fixing : ∀ p ∈ graph, ∀ q ∈ graph, p.1 = p.2 → q.1 ≤ p.1 → q.1 = q.2

namespace FixingPartialAut

variable {α} [LinearOrder α]

instance : Coe (FixingPartialAut α) (PartialIso α α) where
  coe := FixingPartialAut.toPartialIso

def empty : FixingPartialAut α where
  toPartialIso := PartialIso.empty
  fixing := by intro _ h; contradiction

instance : Inhabited (FixingPartialAut α) := ⟨empty⟩

instance : EmptyCollection (FixingPartialAut α) := ⟨empty⟩

def inv (f : FixingPartialAut α) : FixingPartialAut α where
  toPartialIso := f.toPartialIso.symm
  fixing := by
    intro p hp q hq hpq hqa
    simp only [PartialIso.symm, PartialInj.symm, Set.mem_setOf_eq] at hp hq
    have hpfixed : (p.2, p.1) ∈ f.graph := hp
    have hqgraph : (q.2, q.1) ∈ f.graph := hq
    have hpfix : p.2 = p.1 := hpq.symm
    have hqle : q.2 ≤ p.2 := (f.order_pres_iff hqgraph hpfixed).mpr (hpfix ▸ hqa)
    have hqfixed : q.2 = q.1 := f.fixing (p.2, p.1) hpfixed (q.2, q.1) hqgraph hpfix hqle
    exact hqfixed.symm

instance : InvolutiveInv (FixingPartialAut α) where
  inv := inv
  inv_inv f := by ext ⟨a, b⟩; simp [inv, PartialIso.symm, PartialInj.symm]

@[simp]
lemma inv_toPartialIso (f : FixingPartialAut α) : (f⁻¹).toPartialIso = f.toPartialIso.symm := rfl

/-- The result of adding one new pair `(a, b)` to the graph of `f`. -/
structure Extension (f : FixingPartialAut α) (a : α) (b : α) extends FixingPartialAut α where
  spec : graph = f.graph ∪ {⟨a, b⟩}

instance {f : FixingPartialAut α} {a b : α} : CoeOut (f.Extension a b) (FixingPartialAut α) where
  coe := Extension.toFixingPartialAut

/-- `f.CanExtend a b` holds when `(a, b)` can be added to `f` while preserving the fixing
property. Besides the conditions from `PartialIso.CanExtend`, the new pair must be compatible
with all existing fixed points:
- if `a = b` (the new pair is a fixed point), then all pairs `(c, d)` with `c ≤ a`
  must satisfy `c = d`.
- if there exists a fixed point `(c, c)` with `a ≤ c`, then `a = b`. -/
structure CanExtend (f : FixingPartialAut α) (a b : α) : Prop
      extends toCanExtendIso : f.toPartialIso.CanExtend a b where
    fixingCompat : (a = b → ∀ p ∈ f.graph, p.1 ≤ a → p.1 = p.2) ∧
                   (∀ p ∈ f.graph, p.1 = p.2 → a ≤ p.1 → a = b)

/-- Construct the extension of `f` by `(a, b)`, given a `CanExtend` proof. -/
def CanExtend.toExtension {f : FixingPartialAut α} {a : α} {b : α}
  (h : f.CanExtend a b) : f.Extension a b :=
  have g_ext := h.toCanExtendIso.toExtension
  {
    graph := g_ext.graph
    functional := g_ext.functional
    injective := g_ext.injective
    order_pres := g_ext.order_pres
    fixing := by
      intro p hp q hq hpq hqa
      by_cases hpf : p ∈ f.graph <;> by_cases hqf : q ∈ f.graph
      · -- Both p and q in f.graph
        exact f.fixing p hpf q hqf hpq hqa
      · -- p in f.graph, q not in f.graph (so q = (a, b))
        rw [g_ext.spec, Set.mem_union] at hq
        cases hq with
        | inl hqf' => exact absurd hqf' hqf
        | inr hq => obtain rfl := Set.mem_singleton_iff.mp hq
                    exact h.fixingCompat.2 p hpf hpq hqa
      · -- p not in f.graph (so p = (a, b)), q in f.graph
        rw [g_ext.spec, Set.mem_union] at hp
        cases hp with
        | inl hpf' => exact absurd hpf' hpf
        | inr hp' => obtain rfl := Set.mem_singleton_iff.mp hp'
                     exact h.fixingCompat.1 hpq q hqf hqa
      · -- Both p and q not in f.graph (so both = (a, b))
        rw [g_ext.spec, Set.mem_union] at hp hq
        cases hp with
        | inl hpf' => exact absurd hpf' hpf
        | inr hp' => obtain rfl := Set.mem_singleton_iff.mp hp'
                     cases hq with
                     | inl hqf' => exact absurd hqf' hqf
                     | inr hq' => obtain rfl := Set.mem_singleton_iff.mp hq'; exact hpq
    spec := g_ext.spec
  }

end FixingPartialAut
