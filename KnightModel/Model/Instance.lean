/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.Model.Basic
import KnightModel.Model.ModelIso

/-!
# Knight Model Instances

This file constructs two canonical `KnightModel` instances.

## Strict initial segments

Given a `KnightModel α Ω`, the strict initial segment `{x : α // x < a}` below any `a : α`
inherits a `KnightModel` structure via restriction of the blueprint action. The action stays
within the fiber because `fn n` is a retraction (`fn n x ≤ x < a`).

As a consequence, every strict (or closed) initial segment of a knight model is **countable**,
since `capture` gives a surjection from the countable type `Ω` onto each closed segment.

## Blueprint model

For any `Blueprint Ω`, the subtype `Blueprint.Model Ω := {n : Ω // n < 1}` carries a
canonical `KnightModel` structure with `fn n a = n * a`. This is the "standard" model associated
to a blueprint, and it is countable (as a subtype of the countable `Ω`).

## Main definitions

* `KnightModel.InitialSegment α a`: the strict initial segment `{x : α // x < a}`
* `KnightModel.instKnightModelInitialSegment`: `KnightModel` instance for `InitialSegment`
* `KnightModel.countable_initialSegment`: every `InitialSegment` is countable
* `Blueprint.Model`: the canonical model `{n : Ω // n < 1}`
* `Blueprint.Model.instKnightModel`: `KnightModel` instance for `Model`

## Tags

knight model, initial segment, blueprint model, countable
-/

namespace KnightModel

variable {α Ω : Type 0} [Blueprint Ω] [KnightModel α Ω]

/-- The strict initial segment below `a`. -/
abbrev InitialSegment (α : Type*) [LT α] (a : α) := {x : α // x < a}

instance (a : α) : DenselyOrdered (InitialSegment α a) where
  dense x y hxy := by
    obtain ⟨z, hxz, hzy⟩ := DenselyOrdered.dense x.1 y.1 hxy
    exact ⟨⟨z, lt_trans hzy y.2⟩, hxz, hzy⟩

instance (a : α) : NoMinOrder (InitialSegment α a) where
  exists_lt x := by
    obtain ⟨y, hyx⟩ := exists_lt x.1
    exact ⟨⟨y, lt_trans hyx x.2⟩, hyx⟩

instance (a : α) : NoMaxOrder (InitialSegment α a) where
  exists_gt x := by
    obtain ⟨y, hxy, hya⟩ := DenselyOrdered.dense x.1 a x.2
    exact ⟨⟨y, hya⟩, hxy⟩

/-- Restriction of the model action to the strict initial segment below `a`. -/
def initialFn (a : α) (n : Ω) : InitialSegment α a → InitialSegment α a
  | x => ⟨KnightModel.fn n x.1, lt_of_le_of_lt (KnightModel.dec n x.1) x.2⟩

instance instKnightModelInitialSegment (a : α) : KnightModel (InitialSegment α a) Ω where
  fn := initialFn (α := α) a
  capture x y hxy := by
    obtain ⟨n, hn⟩ := KnightModel.capture (α := α) (Ω := Ω) x.1 y.1 hxy
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa [initialFn] using hn
  blueprint_ord m n x := by
    simpa [initialFn] using (KnightModel.blueprint_ord (α := α) (Ω := Ω) m n x.1)
  blueprint_comp m n x := by
    apply Subtype.ext
    simpa [initialFn] using (KnightModel.blueprint_comp (α := α) (Ω := Ω) m n x.1)

/-- The closed initial segment below `a` is countable. -/
theorem countable_initialSegment_le (a : α) : Countable {x : α // x ≤ a} := by
  let f : Ω → {x : α // x ≤ a} := fun n => ⟨KnightModel.fn n a, KnightModel.dec n a⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨n, hn⟩ := KnightModel.capture (α := α) (Ω := Ω) x.1 a x.2
    exact ⟨n, Subtype.ext hn⟩
  exact Function.Surjective.countable hsurj

/-- The strict initial segment below `a` is countable. -/
theorem countable_initialSegment (a : α) : Countable (InitialSegment α a) := by
  let g : InitialSegment α a → {x : α // x ≤ a} := fun x => ⟨x.1, le_of_lt x.2⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => z.1) hxy
  haveI : Countable {x : α // x ≤ a} := countable_initialSegment_le (α := α) (Ω := Ω) a
  exact Function.Injective.countable hg

instance instCountableInitialSegment (a : α) : Countable (InitialSegment α a) :=
  countable_initialSegment (α := α) (Ω := Ω) a

/-- The inclusion of a strict initial segment as a `KnightEmbedding`. -/
def initialSegmentInclusion (a : α) : InitialSegment α a →ₖ[Ω] α where
  toRelEmbedding := {
    toEmbedding := Function.Embedding.subtype (· < a)
    map_rel_iff' := Iff.rfl
  }
  fn_comm := fun _ _ => rfl

end KnightModel

/-! ## Knight Model from a Knight Blueprint -/

namespace Blueprint

variable {Ω : Type 0} [Blueprint Ω]

/-- The canonical knight model derived from a knight blueprint:
the set of elements strictly less than 1. -/
def Model (Ω : Type 0) [Blueprint Ω] := {n : Ω // n < 1}

namespace Model

instance : LinearOrder (Model Ω) :=
  Subtype.instLinearOrder _

instance : DenselyOrdered (Model Ω) where
  dense a b hab := by
    obtain ⟨c, hac, hcb⟩ := DenselyOrdered.dense a.val b.val hab
    exact ⟨⟨c, lt_trans hcb b.property⟩, hac, hcb⟩

instance : NoMinOrder (Model Ω) where
  exists_lt a := by
    obtain ⟨b, hb⟩ := exists_lt a.val
    exact ⟨⟨b, lt_trans hb a.property⟩, hb⟩

instance : NoMaxOrder (Model Ω) where
  exists_gt a := by
    obtain ⟨c, hac, hc1⟩ := DenselyOrdered.dense a.val 1 a.property
    exact ⟨⟨c, hc1⟩, hac⟩

/-- The action of a blueprint element on the model: `fn n a = n * a`. -/
def fn (n : Ω) (a : Model Ω) : Model Ω :=
  ⟨n * a.val, lt_of_le_of_lt (mul_le_right n a.val) a.property⟩

instance instKnightModel : KnightModel (Model Ω) Ω where
  fn := fn
  capture a b hab := by
    obtain ⟨c, hc⟩ := exists_left_factor hab
    exact ⟨c, Subtype.ext hc.symm⟩
  blueprint_ord m n a := by
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      exact absurd (mul_right_cancel (le_antisymm h (mul_le_mul_right a.val hlt.le)))
        hlt.ne'
    · exact fun h => mul_le_mul_right a.val h
  blueprint_comp m n a := Subtype.ext (mul_assoc m n a.val).symm

end Model

end Blueprint
