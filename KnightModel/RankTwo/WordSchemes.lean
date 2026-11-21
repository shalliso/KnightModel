import KnightModel.RankTwo.WordIntervals
import Mathlib.Tactic.DeriveCountable

/-!
# The countable coordinate language

A word parameter is specified by its length in the scheme. Its letters occur
consecutively in the parameter tuple. Composition, finite union, and converse
act on graphs, so no choices of algorithms enter graph equality.
-/

namespace KnightModel.RankTwo

open Set

/-- Schemes have no alphabet or ordinal constants. -/
inductive WordScheme where
  | id | empty
  | prefix (n : ℕ) | through (n : ℕ)
  | interval (m n : ℕ) | tail (n : ℕ)
  | atMost (n : ℕ) | above (n : ℕ)
  | seq (f g : WordScheme) | union (f g : WordScheme) | inv (f : WordScheme)
  deriving Countable

namespace WordScheme

/-- Total number of letter parameters in the scheme. -/
def arity : WordScheme → ℕ
  | .id | .empty => 0
  | .prefix n | .through n | .tail n | .atMost n | .above n => n
  | .interval m n => m+n
  | .seq f g | .union f g => f.arity + g.arity
  | .inv f => f.arity

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- Interpret a scheme as a relation on words, with one flat tuple of letters. -/
def Rel : WordScheme → List A → Word A → Word A → Prop
  | .id, _, x, y => x = y
  | .empty, _, _, _ => False
  | .prefix _, p, x, y => Word.prepend p x = y
  | .through _, p, x, y => Word.through shift p x = y
  | .interval m _, p, x, y =>
    ∃ h : @LT.lt (Word A) _ (p.take m) (p.drop m),
    ∃ z : Ioi (Word.cons o Word.root), x = z.val ∧
      y = (Word.H shift o d hd upper _ _ h z).val
  | .tail _, p, x, y =>
    ∃ h : (p : Word A) ≠ Word.root, ∃ z : Ioi (Word.cons o Word.root),
      x = z.val ∧ y = (Word.tailIso shift o d hd upper p h z).val
  | .atMost _, p, x, y => x ≤ (p : Word A) ∧ x = y
  | .above _, p, x, y => @LT.lt (Word A) _ p x ∧ x = y
  | .seq f g, p, x, y =>
    ∃ z, Rel f (p.take f.arity) x z ∧ Rel g (p.drop f.arity) z y
  | .union f g, p, x, y =>
    Rel f (p.take f.arity) x y ∨ Rel g (p.drop f.arity) x y
  | .inv f, p, x, y => Rel f p y x

end WordScheme

namespace Word

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- A graph admitting a scheme together with exactly its finite tuple of parameters. -/
def Schematic (r : Word A → Word A → Prop) : Prop :=
  ∃ (c : WordScheme) (p : List A), p.length = c.arity ∧
    ∀ x y, c.Rel shift o d hd upper p x y ↔ r x y

variable {shift o d hd upper} {r s t : Word A → Word A → Prop}

theorem Schematic.congr (hr : Schematic shift o d hd upper r)
    (h : ∀ x y, r x y ↔ s x y) : Schematic shift o d hd upper s := by
  obtain ⟨c,p,hp,hc⟩ := hr
  exact ⟨c,p,hp,fun x y => (hc x y).trans (h x y)⟩

theorem Schematic.seq (hr : Schematic shift o d hd upper r)
    (hs : Schematic shift o d hd upper s) :
    Schematic shift o d hd upper (fun x y => ∃ z, r x z ∧ s z y) := by
  obtain ⟨c,p,hp,hc⟩ := hr
  obtain ⟨e,q,hq,he⟩ := hs
  refine ⟨.seq c e, p ++ q, by simp [WordScheme.arity,hp,hq], ?_⟩
  intro x y
  simp only [WordScheme.Rel, ← hp, List.take_left, List.drop_left, hc, he]

theorem Schematic.union (hr : Schematic shift o d hd upper r)
    (hs : Schematic shift o d hd upper s) :
    Schematic shift o d hd upper (fun x y => r x y ∨ s x y) := by
  obtain ⟨c,p,hp,hc⟩ := hr
  obtain ⟨e,q,hq,he⟩ := hs
  refine ⟨.union c e, p ++ q, by simp [WordScheme.arity,hp,hq], ?_⟩
  intro x y
  simp only [WordScheme.Rel, ← hp, List.take_left, List.drop_left, hc, he]

theorem Schematic.inv (hr : Schematic shift o d hd upper r) :
    Schematic shift o d hd upper (fun x y => r y x) := by
  obtain ⟨c,p,hp,hc⟩ := hr
  exact ⟨.inv c, p, hp, fun x y => hc y x⟩

variable (shift o d hd upper)

theorem schematic_id : Schematic shift o d hd upper (· = ·) :=
  ⟨.id, [], rfl, fun _ _ => Iff.rfl⟩

theorem schematic_empty : Schematic shift o d hd upper (fun _ _ => False) :=
  ⟨.empty, [], rfl, fun _ _ => Iff.rfl⟩

theorem schematic_prefix (p : List A) :
    Schematic shift o d hd upper (fun x y => prepend p x = y) :=
  ⟨.prefix p.length, p, rfl, fun _ _ => Iff.rfl⟩

theorem schematic_through (p : Word A) :
    Schematic shift o d hd upper (fun x y => through shift p x = y) :=
  ⟨.through (List.length p), p, rfl, fun _ _ => Iff.rfl⟩

theorem schematic_H (v u : Word A) :
    Schematic shift o d hd upper (fun x y => ∃ h : v < u, ∃ z : Ioi (cons o root),
      x = z.val ∧ y = (H shift o d hd upper v u h z).val) := by
  refine ⟨.interval (List.length v) (List.length u), List.append v u, List.length_append, ?_⟩
  intro x y
  have ht : List.take (List.length v) (List.append v u) = v := List.take_left
  have hb : List.drop (List.length v) (List.append v u) = u := List.drop_left
  let R (l t : Word A) := ∃ h : l < t, ∃ z : Ioi (cons o root),
    x = z.val ∧ y = (H shift o d hd upper l t h z).val
  change R (List.take (List.length v) (List.append v u)) (List.drop (List.length v) (List.append v u)) ↔ R v u
  exact Iff.of_eq (congrArg₂ R ht hb)

theorem schematic_tail (v : Word A) :
    Schematic shift o d hd upper (fun x y => ∃ h : v ≠ root, ∃ z : Ioi (cons o root),
      x = z.val ∧ y = (tailIso shift o d hd upper v h z).val) :=
  ⟨.tail (List.length v), v, rfl, fun _ _ => Iff.rfl⟩

theorem schematic_atMost (p : Word A) :
    Schematic shift o d hd upper (fun x y => x ≤ p ∧ x = y) :=
  ⟨.atMost (List.length p), p, rfl, fun _ _ => Iff.rfl⟩

theorem schematic_above (p : Word A) :
    Schematic shift o d hd upper (fun x y => p < x ∧ x = y) :=
  ⟨.above (List.length p), p, rfl, fun _ _ => Iff.rfl⟩

end Word
end KnightModel.RankTwo
