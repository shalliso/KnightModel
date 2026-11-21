import KnightModel.RankTwo.MarkedExtensionLimit

/-! # Countable marked diagrams and their elementary unions

The arrows of a marked square are embeddings. Only the distinguished point
must remain outside the new base. Other points may enter the new base.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal

variable {R : Nat → Type}

/-- A specified point outside an elementary copy of the base. -/
structure Pointed (B : World R) where
  target : World R
  embed : Elementary B.model target.model
  mark : target.carrier
  fresh : ∀ x, embed x ≠ mark

/-- A countable union is taken simultaneously on the two sides of a sequence
of marked diagrams. Commutativity and preservation of the distinguished
point are the only compatibility conditions. -/
structure MarkedChain (R : Nat → Type) (I : Type) [LinearOrder I] where
  base : Tower R I
  top : Tower R I
  embed : ∀ i, Elementary (base.world i).model (top.world i).model
  mark : ∀ i, (top.world i).carrier
  fresh : ∀ i x, embed i x ≠ mark i
  comm : ∀ {i j} (h : i ≤ j) x, top.map h (embed i x) = embed j (base.map h x)
  keep : ∀ {i j} (h : i ≤ j), top.map h (mark i) = mark j

namespace MarkedChain

variable {I : Type} [LinearOrder I] (Z : MarkedChain R I)

def stage (i : I) : Pointed (Z.base.world i) := ⟨Z.top.world i,Z.embed i,Z.mark i,Z.fresh i⟩

variable [Nonempty I]

def limitEmbed : Elementary Z.base.limit.model Z.top.limit.model :=
  Z.base.descend (fun i => (Z.embed i).comp (Z.top.into i)) (by
    intro i j h x
    change Z.top.into i (Z.embed i x) = Z.top.into j (Z.embed j (Z.base.map h x))
    rw [← Z.comm h,Z.top.into_map])

theorem limitEmbed_into (i : I) (x : (Z.base.world i).carrier) :
    Z.limitEmbed (Z.base.into i x) = Z.top.into i (Z.embed i x) := rfl

omit [Nonempty I] in
theorem common_mark (i j : I) : Z.top.into i (Z.mark i) = Z.top.into j (Z.mark j) := by
  rw [← Z.top.into_map (le_max_left i j) (Z.mark i),
    ← Z.top.into_map (le_max_right i j) (Z.mark j),Z.keep,Z.keep]

/-- The union point cannot equal the image of a base element: that element
comes from some stage, where the common point is still outside the base. -/
noncomputable def union : Pointed Z.base.limit where
  target := Z.top.limit
  embed := Z.limitEmbed
  mark := Z.top.into (Classical.choice ‹Nonempty I›) (Z.mark _)
  fresh := by
    intro x
    obtain ⟨i,y,rfl⟩ := Z.base.exhausts x
    change Z.top.into i (Z.embed i y) ≠ _
    rw [← Z.common_mark i (Classical.choice ‹Nonempty I›)]
    exact fun he => Z.fresh i y ((Z.top.into i).injective he)

theorem union_mark (i : I) : Z.top.into i (Z.mark i) = Z.union.mark := Z.common_mark i _

end MarkedChain

/-- A class of countable marked elementary extensions of a sentence. Its
union axiom ranges only over countable chains of countable diagrams. -/
structure Family (φ : Formula R 0) where
  member : {B : World R} → Pointed B → Prop
  seed : ∃ (B : World R) (p : Pointed B), member p
  smallBase : ∀ {B} {p : Pointed B}, member p → Countable B.carrier
  smallTarget : ∀ {B} {p : Pointed B}, member p → Countable p.target.carrier
  satisfies : ∀ {B} {p : Pointed B}, member p → BackAndForth.Satisfies B.model φ
  invariant : ∀ {B E} (p : Pointed B) (q : Pointed E),
    (u : Elementary B.model E.model) → (v : Elementary p.target.model q.target.model) →
    Function.Surjective u → Function.Surjective v →
    (∀ x, v (p.embed x) = q.embed (u x)) → v p.mark = q.mark → member p → member q
  change : ∀ {B E} (p : Pointed B), member p → Countable E.carrier →
    BackAndForth.Satisfies E.model φ → (u : Elementary B.model E.model) →
    ∃ q : Pointed E, member q ∧ ∃ v : Elementary p.target.model q.target.model,
      (∀ x, v (p.embed x) = q.embed (u x)) ∧ v p.mark = q.mark
  closed : ∀ {I : Type} [LinearOrder I] [WellFoundedLT I] [Nonempty I] [Countable I] (Z : MarkedChain R I),
    (∀ i, member (Z.stage i)) → member Z.union

end KnightModel.RankTwo.Scott.MarkedExtension
