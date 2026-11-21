import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.WellFounded

/-! # Transfinite construction of coherent towers

The objects and arrows may live in different universes. The local extension
rule sees the entire diagram strictly below the new index. It supplies maps
from all its objects into a new one, with commuting triangles. A stagewise
property of this entire family of incoming maps survives the recursion.
-/

namespace KnightModel.RankTwo.Transfinite

universe u v w
variable {O : Type u} (H : O → O → Type v)
variable (compose : ∀ {a b c}, H a b → H b c → H a c)

/-- A directed diagram presented by its strict transition arrows. -/
structure Diagram (J : Type w) [Preorder J] where
  obj : J → O
  map : ∀ {i j}, i < j → H (obj i) (obj j)
  trans : ∀ {i j k} (ij : i < j) (jk : j < k),
    compose (map ij) (map jk) = map (lt_trans ij jk)

/-- A compatible family of maps from the whole diagram to one object. -/
structure Apex {J : Type w} [Preorder J] (D : Diagram H compose J) where
  obj : O
  leg : ∀ i, H (D.obj i) obj
  comm : ∀ {i j} (ij : i < j), compose (D.map ij) (leg j) = leg i

variable {J : Type w} [Preorder J]

/-- Extra structure at a new stage can depend on every incoming map, for
example the existence of a point outside all earlier images. -/
abbrev StageProperty := ∀ j : J, ∀ old : Set.Iio j → O, ∀ new : O,
  (∀ i, H (old i) new) → Prop

private abbrev ArrowCode := (a : O) × (b : O) × H a b

private def pack {a b : O} (f : H a b) : ArrowCode H := ⟨a, b, f⟩

private theorem pack_inj {a b : O} {f g : H a b} (h : pack H f = pack H g) : f = g := by
  simpa [pack] using h

/-- The endpoints are stored on an arrow solely to define the recursion
before its coherence proof. -/
private structure Raw (I : Type w) where
  obj : O
  edge : I → Option (ArrowCode H)

private def Local (P : StageProperty H (J := J)) (j : J)
    (old : Set.Iio j → Raw H J) (new : Raw H J) : Prop :=
  ∃ legs : ∀ i, H (old i).obj new.obj,
    (∀ i, new.edge i.val = some (pack H (legs i))) ∧
    (∀ (i k : Set.Iio j) (ik : i < k) (f : H (old i).obj (old k).obj),
      (old k).edge i.val = some (pack H f) → compose f (legs k) = legs i) ∧
    P j (fun i => (old i).obj) new.obj legs

/-- A predicate over the whole strict history can be realized by
well-founded recursion whenever it extends every correct history. -/
private theorem history_recursion [WellFoundedLT J] {V : Type*} (start : V)
    (P : ∀ j : J, (Set.Iio j → V) → V → Prop)
    (step : ∀ j (s : Set.Iio j → V),
      (∀ i, P i.val (fun z => s ⟨z.val, lt_trans z.property i.property⟩) (s i)) →
        ∃ v, P j s v) : ∃ s : J → V, ∀ j, P j (fun i => s i.val) (s j) := by
  classical
  let pick (j : J) (s : Set.Iio j → V) : V := if h : ∃ v, P j s v then h.choose else start
  let s : J → V := wellFounded_lt.fix fun j f => pick j (fun i => f i.val i.property)
  refine ⟨s, fun i => (wellFounded_lt (α := J)).induction (C := fun j => P j (fun i => s i.val) (s j)) i ?_⟩
  intro j ih
  have ok := step j (fun i => s i.val) (fun i => ih i.val (Set.mem_Iio.mp i.property))
  have eq : s j = pick j (fun i => s i.val) := by
    change wellFounded_lt.fix _ j = _
    rw [WellFounded.fix_eq]
  exact eq ▸ (show P j (fun i => s i.val) (pick j (fun i => s i.val)) by
    simpa only [pick, dif_pos ok] using ok.choose_spec)

/-- Build a coherent diagram over any well-founded preorder, preserving
the required apex property at every index, including limits. -/
theorem build [WellFoundedLT J] (start : O) (P : StageProperty H (J := J))
    (step : ∀ j : J, ∀ D : Diagram H compose (Set.Iio j),
      ∃ c : Apex H compose D, P j D.obj c.obj c.leg) :
    ∃ D : Diagram H compose J, ∀ j,
      P j (fun i => D.obj i.val) (D.obj j) (fun i => D.map i.property) := by
  classical
  let cert := Local H compose P
  have advance (j : J) (s : Set.Iio j → Raw H J)
      (prev : ∀ i, cert i.val (fun z => s ⟨z.val, lt_trans z.property i.property⟩) (s i)) :
      ∃ q, cert j s q := by
    let m {i k : Set.Iio j} (ik : i < k) : H (s i).obj (s k).obj :=
      (prev k).choose ⟨i.val, ik⟩
    have recorded {i k : Set.Iio j} (ik : i < k) :
        (s k).edge i.val = some (pack H (m ik)) := (prev k).choose_spec.1 ⟨i.val, ik⟩
    let D : Diagram H compose (Set.Iio j) := {
      obj := fun i => (s i).obj
      map := m
      trans := fun {i k l} ik kl => (prev l).choose_spec.2.1
        ⟨i.val, lt_trans ik kl⟩ ⟨k.val, kl⟩ ik (m ik) (recorded ik) }
    obtain ⟨c, good⟩ := step j D
    let q : Raw H J := ⟨c.obj, fun i => if h : i < j then some (pack H (c.leg ⟨i,h⟩)) else none⟩
    refine ⟨q, c.leg, fun i => by simp [q, Set.mem_Iio.mp i.property], ?_, good⟩
    intro i k ik f hf
    have eq : m ik = f := pack_inj H (Option.some.inj ((recorded ik).symm.trans hf))
    exact eq ▸ c.comm ik
  obtain ⟨s, ok⟩ := history_recursion (J := J) (⟨start,fun _ => none⟩ : Raw H J) cert advance
  let m {i j : J} (h : i < j) : H (s i).obj (s j).obj := (ok j).choose ⟨i,h⟩
  have recorded {i j : J} (h : i < j) : (s j).edge i = some (pack H (m h)) :=
    (ok j).choose_spec.1 ⟨i,h⟩
  let D : Diagram H compose J := {
    obj := fun i => (s i).obj
    map := m
    trans := fun {i j k} ij jk => (ok k).choose_spec.2.1
      ⟨i,lt_trans ij jk⟩ ⟨j,jk⟩ ij (m ij) (recorded ij) }
  exact ⟨D, fun j => (ok j).choose_spec.2.2⟩

end KnightModel.RankTwo.Transfinite
