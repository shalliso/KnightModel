/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Basic
import KnightModel.PartialIso
/-!
# Knight Model Morphisms

This file defines morphisms between Knight models: embeddings, isomorphisms, and partial
isomorphisms (for back-and-forth arguments).

## Main definitions

* `KnightEmbedding α β Ω`: An order-embedding `α ↪o β` that commutes with the blueprint action.
* `KnightIso α β Ω`: An order-isomorphism `α ≃o β` that commutes with the blueprint action.
* `PartialKnightIso α β Ω`: A partial order-isomorphism compatible with the blueprint action.

## Tags

knight model, embedding, isomorphism, partial isomorphism, back-and-forth
-/

/-! ## Knight Embeddings -/

/-- A `KnightEmbedding` is an order-embedding between Knight models that commutes with
the blueprint action: applying `fn` before or after embedding gives the same result. -/
@[ext]
structure KnightEmbedding (α β Ω : Type 0) [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] extends α ↪o β where
  fn_comm : ∀ n : Ω, ∀ a : α,
    toFun (KnightModel.fn n a) = KnightModel.fn n (toFun a)

notation:25 α " →ₖ[" Ω "] " β => KnightEmbedding α β Ω

namespace KnightEmbedding

variable {α β γ Ω : Type 0} [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] [KnightModel γ Ω]

/-- `KnightEmbedding` has a `FunLike` instance via the underlying order embedding. -/
instance : FunLike (α →ₖ[Ω] β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f; cases g
    simp only [KnightEmbedding.mk.injEq]
    exact RelEmbedding.ext (fun x => congr_fun h x)

/-- The identity `KnightEmbedding`. -/
def id : α →ₖ[Ω] α where
  toRelEmbedding := RelEmbedding.refl _
  fn_comm := fun _n _a => rfl

@[simp]
lemma id_apply (a : α) : (id : α →ₖ[Ω] α) a = a := rfl

/-- Composition of `KnightEmbedding`s. -/
def comp (f : β →ₖ[Ω] γ) (g : α →ₖ[Ω] β) : α →ₖ[Ω] γ where
  toRelEmbedding := g.toRelEmbedding.trans f.toRelEmbedding
  fn_comm := fun n a => by
    change f.toFun (g.toFun (KnightModel.fn n a)) = KnightModel.fn n (f.toFun (g.toFun a))
    rw [g.fn_comm, f.fn_comm]

@[simp]
lemma comp_apply (f : β →ₖ[Ω] γ) (g : α →ₖ[Ω] β) (a : α) :
    comp f g a = f (g a) := rfl

scoped[KnightEmbedding] infixr:90 " ∘ " => KnightEmbedding.comp

/-- `KnightEmbedding` commutes with the blueprint action, stated via the `FunLike` coercion.
Use this as a `simp` lemma instead of reaching into `fn_comm` directly. -/
@[simp]
lemma map_fn (f : α →ₖ[Ω] β) (n : Ω) (a : α) :
    f (KnightModel.fn n a) = KnightModel.fn n (f a) := f.fn_comm n a

end KnightEmbedding

/-! ## Knight Isomorphisms -/

/-- A `KnightIso` is an order-isomorphism between Knight models that commutes with
the blueprint action: applying `fn` before or after the isomorphism gives the same result. -/
@[ext]
structure KnightIso (α β Ω : Type 0) [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] extends α ≃o β where
  fn_comm : ∀ n : Ω, ∀ a : α,
    toFun (KnightModel.fn n a) = KnightModel.fn n (toFun a)

notation:25 α " ≃ₖ[" Ω "] " β => KnightIso α β Ω

namespace KnightIso

variable {α β Ω : Type 0} [Blueprint Ω] [KnightModel α Ω] [KnightModel β Ω]

/-- The inverse of a `KnightIso`. -/
def symm (f : KnightIso α β Ω) : KnightIso β α Ω where
  toRelIso := f.toRelIso.symm
  fn_comm := by
    intro n a
    apply f.toRelIso.injective
    exact (f.toRelIso.apply_symm_apply _).trans
      ((f.fn_comm n _).trans (congrArg (KnightModel.fn n) (f.toRelIso.apply_symm_apply _))).symm

instance : FunLike (α ≃ₖ[Ω] β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f; cases g
    simp only [KnightIso.mk.injEq]
    exact OrderIso.ext h

/-- `KnightIso` commutes with the blueprint action, stated via the `FunLike` coercion. -/
@[simp]
lemma map_fn (f : KnightIso α β Ω) (n : Ω) (a : α) :
    f (KnightModel.fn n a) = KnightModel.fn n (f a) := f.fn_comm n a

/-- Extract the forward `KnightEmbedding` from a `KnightIso`. -/
def toKnightEmbedding (f : α ≃ₖ[Ω] β) : α →ₖ[Ω] β where
  toRelEmbedding := f.toRelIso.toRelEmbedding
  fn_comm := f.fn_comm

end KnightIso

/-! ## Partial Knight Isomorphisms -/

/-- A `PartialKnightIso` is a partial order-isomorphism between Knight models that is
compatible with the blueprint action: for any blueprint element `n` and any two pairs
`p, q` in the graph, `q.1 = fn n p.1 ↔ q.2 = fn n p.2`. -/
@[ext]
structure PartialKnightIso (α β Ω : Type 0) [Blueprint Ω]
    [KnightModel α Ω] [KnightModel β Ω] extends PartialIso α β where
  fn_compat : ∀ n : Ω, ∀ p ∈ graph, ∀ q ∈ graph,
    q.1 = KnightModel.fn n p.1 ↔ q.2 = KnightModel.fn n p.2

namespace PartialKnightIso

variable {α β Ω : Type 0} [Blueprint Ω] [KnightModel α Ω] [KnightModel β Ω]

/-- A `PartialKnightIso` is finite if its graph is a finite set. -/
def isFinite (f : PartialKnightIso α β Ω) : Prop := f.graph.Finite

/-- The empty partial Knight isomorphism. The fn-compatibility holds vacuously
since the graph is empty. -/
def empty : PartialKnightIso α β Ω where
  toPartialIso := PartialIso.empty
  fn_compat := by
    intro _ _ hp _ _
    simp [PartialIso.empty, PartialInj.empty] at hp

instance : Inhabited (PartialKnightIso α β Ω) := ⟨empty⟩

instance : EmptyCollection (PartialKnightIso α β Ω) := ⟨empty⟩

/-- Symmetric of a `PartialKnightIso`: swap domain and range pairs. -/
def symm (f : PartialKnightIso α β Ω) : PartialKnightIso β α Ω where
  toPartialIso := f.toPartialIso.symm
  fn_compat := by
    intro n p hp q hq
    simp only [PartialIso.symm, PartialInj.symm, Set.mem_setOf_eq] at hp hq
    exact (f.fn_compat n (p.2, p.1) hp (q.2, q.1) hq).symm

@[simp]
lemma symm_symm (f : PartialKnightIso α β Ω) : f.symm.symm = f := by
  ext ⟨a, b⟩
  simp [symm, PartialIso.symm, PartialInj.symm]

/-- Extending a `PartialKnightIso` by one pair `(a, b)`. -/
structure Extension (f : PartialKnightIso α β Ω) (a : α) (b : β)
    extends PartialKnightIso α β Ω where
  spec : graph = f.graph ∪ {⟨a, b⟩}

instance {f : PartialKnightIso α β Ω} {a : α} {b : β} :
    CoeOut (f.Extension a b) (PartialKnightIso α β Ω) where
  coe := Extension.toPartialKnightIso

/-- Conditions under which a `PartialKnightIso` can be extended by adding the pair `(a, b)`.
Besides the order-compatibility from `PartialIso.CanExtend`, we require fn-compatibility
for pairs involving the new point:
- `fnCompatPre`: the new point `a` is the fn-image of some old domain element
  iff `b` is the fn-image of the corresponding range element.
- `fnCompatPost`: some old domain element is the fn-image of `a`
  iff the corresponding range element is the fn-image of `b`. -/
structure CanExtend (f : PartialKnightIso α β Ω) (a : α) (b : β) : Prop
    extends toCanExtendIso : f.toPartialIso.CanExtend a b where
  fnCompatPre : ∀ n : Ω, ∀ p ∈ f.graph,
    a = KnightModel.fn n p.1 ↔ b = KnightModel.fn n p.2
  fnCompatPost : ∀ n : Ω, ∀ p ∈ f.graph,
    p.1 = KnightModel.fn n a ↔ p.2 = KnightModel.fn n b

/-- Construct an `Extension` of a `PartialKnightIso` from a `CanExtend` proof.
The order-compatibility fields are inherited from `PartialIso.CanExtend.toExtension`;
fn-compatibility for the extended graph is left as `sorry`. -/
def CanExtend.toExtension {f : PartialKnightIso α β Ω} {a : α} {b : β}
    (h : f.CanExtend a b) : f.Extension a b :=
  have g_ext := h.toCanExtendIso.toExtension
  { graph      := g_ext.graph
    functional := g_ext.functional
    injective  := g_ext.injective
    order_pres := g_ext.order_pres
    fn_compat  := by
      intro n p hp q hq
      rw [g_ext.spec, Set.mem_union, Set.mem_singleton_iff] at hp hq
      rcases hp with hpf | rfl <;> rcases hq with hqf | rfl
      · -- p ∈ f.graph, q ∈ f.graph
        exact f.fn_compat n p hpf q hqf
      · -- p ∈ f.graph, q = (a, b)
        exact h.fnCompatPre n p hpf
      · -- p = (a, b), q ∈ f.graph
        exact h.fnCompatPost n q hqf
      · -- p = (a, b), q = (a, b)
        -- Both sides reduce to n = 1 via blueprint_ord
        constructor
        · intro ha
          -- ha : a = fn n a; derive n = 1 via blueprint_ord, then fn n b = b
          have h1a : KnightModel.fn (1 : Ω) a = a := KnightModel.fn_one_eq_id a
          have hle : KnightModel.fn (1 : Ω) a ≤ KnightModel.fn n a := le_of_eq (h1a.trans ha)
          have hn1 : n = 1 :=
            le_antisymm (Blueprint.one_le n) ((KnightModel.blueprint_ord n 1 a).mp hle)
          subst hn1
          exact (KnightModel.fn_one_eq_id b).symm
        · intro hb
          -- hb : b = fn n b; derive n = 1 via blueprint_ord, then fn n a = a
          have h1b : KnightModel.fn (1 : Ω) b = b := KnightModel.fn_one_eq_id b
          have hle : KnightModel.fn (1 : Ω) b ≤ KnightModel.fn n b := le_of_eq (h1b.trans hb)
          have hn1 : n = 1 :=
            le_antisymm (Blueprint.one_le n) ((KnightModel.blueprint_ord n 1 b).mp hle)
          subst hn1
          exact (KnightModel.fn_one_eq_id a).symm
    spec       := g_ext.spec }

end PartialKnightIso
