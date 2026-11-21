/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std

/-!
# Infinitary formulas and back-and-forth

Finite contexts exclude infinitely long strings of quantifiers. The branching constructor
is indexed by the natural numbers, so each syntax tree is an actual countable-conjunction
formula. Function symbols can be treated by their graph relations.
-/

namespace KnightModel.RankTwo.Scott

universe u v w

/-- Finite-variable tuples, with the newly quantified variable at position zero. -/
abbrev Tuple (M : Type v) (n : Nat) := Fin n → M

def push {M : Type v} {n : Nat} (x : M) (t : Tuple M n) : Tuple M (n+1) :=
  Fin.cases x t

/-- Atomic tests include variable identifications and all applications of relation symbols. -/
inductive Atom (R : Nat → Type u) (n : Nat) where
  | eq (i j : Fin n)
  | rel {k : Nat} (r : R k) (vars : Fin k → Fin n)

/-- A relational structure on a specified carrier. -/
abbrev Model (R : Nat → Type u) (M : Type v) :=
  ∀ {k : Nat}, R k → Tuple M k → Prop

def Atom.Holds {R : Nat → Type u} {M : Type v} (D : Model R M) {n : Nat}
    (t : Tuple M n) : Atom R n → Prop
  | .eq i j => t i = t j
  | .rel r s => D r (t ∘ s)

/-- Relational syntax for countable infinitary logic with finitely many free variables. -/
inductive Formula (R : Nat → Type u) : Nat → Type u where
  | top {n} : Formula R n
  | atom {n} (p : Atom R n) : Formula R n
  | neg {n} (p : Formula R n) : Formula R n
  | conj {n} (p : Nat → Formula R n) : Formula R n
  | ex {n} (p : Formula R (n+1)) : Formula R n

def Formula.Holds {R : Nat → Type u} {M : Type v} (D : Model R M) :
    {n : Nat} → Formula R n → Tuple M n → Prop
  | _, .top, _ => True
  | _, .atom p, t => p.Holds D t
  | _, .neg p, t => ¬ p.Holds D t
  | _, .conj p, t => ∀ i, (p i).Holds D t
  | _, .ex p, t => ∃ x, p.Holds D (push x t)

/-- The same concrete tuple relation must preserve atoms and answer every move. -/
structure BackAndForth {R : Nat → Type u} {M : Type v} {N : Type w}
    (D : Model R M) (E : Model R N) where
  matchTuples : {n : Nat} → Tuple M n → Tuple N n → Prop
  atoms : ∀ {n} {s : Tuple M n} {t : Tuple N n}, matchTuples s t →
    ∀ p : Atom R n, p.Holds D s ↔ p.Holds E t
  forth : ∀ {n} {s : Tuple M n} {t : Tuple N n}, matchTuples s t →
    ∀ x : M, ∃ y : N, matchTuples (push x s) (push y t)
  back : ∀ {n} {s : Tuple M n} {t : Tuple N n}, matchTuples s t →
    ∀ y : N, ∃ x : M, matchTuples (push x s) (push y t)

namespace BackAndForth

variable {R : Nat → Type u} {M : Type v} {N : Type w} {D : Model R M} {E : Model R N}

/-- Every countable infinitary formula agrees on tuples matched by the system. -/
theorem holds_iff (B : BackAndForth D E) {n : Nat} (p : Formula R n)
    {s : Tuple M n} {t : Tuple N n} (h : B.matchTuples s t) :
    p.Holds D s ↔ p.Holds E t := by
  induction p with
  | top => rfl
  | atom p => exact B.atoms h p
  | neg p ih => exact not_congr (ih h)
  | conj ps ih => exact forall_congr' fun i => ih i h
  | ex p ih =>
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := B.forth h x
      exact ⟨y, (ih hy).mp hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := B.back h y
      exact ⟨x, (ih hx).mpr hy⟩

def Satisfies (D : Model R M) (p : Formula R 0) : Prop := p.Holds D Fin.elim0

theorem sentence_iff (B : BackAndForth D E)
    (h : B.matchTuples (n := 0) Fin.elim0 Fin.elim0) (p : Formula R 0) :
    Satisfies D p ↔ Satisfies E p := B.holds_iff p h

end BackAndForth

end KnightModel.RankTwo.Scott
