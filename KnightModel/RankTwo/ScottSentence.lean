/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import KnightModel.RankTwo.Scott

/-!
# The Scott sentence from tuple-isolating formulas

Inside a countable source, a single formula isolates each complete infinitary tuple
type: choose one distinguishing formula for each tuple with a different type. The
Scott sentence says that tuples carrying these labels obey the full atomic diagrams
and the one-point extension axioms in both directions.
-/

namespace KnightModel.RankTwo.Scott

universe u v w

namespace Formula

variable {R : Nat → Type u} {M : Type v} {n : Nat}

def and (p q : Formula R n) : Formula R n := .conj (fun | 0 => p | _+1 => q)
def implies (p q : Formula R n) : Formula R n := .neg (and p (.neg q))
def disj (p : Nat → Formula R n) : Formula R n := .neg (.conj fun i => .neg (p i))
def all (p : Formula R (n+1)) : Formula R n := .neg (.ex (.neg p))

@[simp] theorem holds_and (D : Model R M) (t : Tuple M n) (p q : Formula R n) :
    (and p q).Holds D t ↔ p.Holds D t ∧ q.Holds D t := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · intro h i; cases i with | zero => exact h.1 | succ _ => exact h.2

@[simp] theorem holds_implies (D : Model R M) (t : Tuple M n) (p q : Formula R n) :
    (implies p q).Holds D t ↔ (p.Holds D t → q.Holds D t) := by
  change (¬ (and p (.neg q)).Holds D t) ↔ _
  rw [holds_and]; change (¬ (_ ∧ ¬ _)) ↔ _; classical constructor
  · exact fun h hp => Classical.byContradiction fun hq => h ⟨hp, hq⟩
  · exact fun h hpair => hpair.2 (h hpair.1)

@[simp] theorem holds_disj (D : Model R M) (t : Tuple M n) (p : Nat → Formula R n) :
    (disj p).Holds D t ↔ ∃ i, (p i).Holds D t := by
  change (¬ ∀ i, ¬ _) ↔ _; classical exact Classical.not_forall_not

@[simp] theorem holds_all (D : Model R M) (t : Tuple M n) (p : Formula R (n+1)) :
    (all p).Holds D t ↔ ∀ x, p.Holds D (push x t) := by
  change (¬ ∃ x, ¬ _) ↔ _; classical simp

/-- Bind every remaining free variable. -/
def close : {n : Nat} → Formula R n → Formula R 0
  | 0, p => p
  | n + 1, p => close (n := n) (all p)

@[simp] theorem satisfies_close (D : Model R M) {n : Nat} (p : Formula R n) :
    BackAndForth.Satisfies D p.close ↔ ∀ t, p.Holds D t := by
  induction n with
  | zero =>
    constructor
    · intro h t
      have e : t = Fin.elim0 := funext fun i => i.elim0
      rwa [e]
    · intro h; exact h _
  | succ n ih =>
    rw [close, ih]
    simp only [holds_all]
    constructor
    · intro h t
      have e : push (t 0) (fun i => t i.succ) = t :=
        funext fun i => Fin.cases rfl (fun _ => rfl) i
      exact e ▸ h _ _
    · intro h t x; exact h _

end Formula

/-- The enumerations needed to write countable conjunctions. Atoms may be absent
in a context, hence the optional entries. -/
structure Presentation (R : Nat → Type u) (M : Type v) where
  enum : Nat → M
  onto : ∀ x, ∃ i, enum i = x
  tuples : ∀ n, Nat → Tuple M n
  tuples_onto : ∀ {n} (s : Tuple M n), ∃ i, tuples n i = s
  atoms : ∀ n, Nat → Option (Atom R n)
  atoms_onto : ∀ {n} (a : Atom R n), ∃ i, atoms n i = some a

namespace Presentation

variable {R : Nat → Type u} {M : Type v} {N : Type w}

def TheoryEq (D : Model R M) {n : Nat} (s t : Tuple M n) : Prop :=
  ∀ p : Formula R n, p.Holds D s ↔ p.Holds D t

/-- Choose a true-on-source, false-on-target separator if one exists. -/
noncomputable def separator (D : Model R M) {n : Nat} (s t : Tuple M n) : Formula R n :=
  open Classical in
  if h : ∃ p : Formula R n, p.Holds D s ∧ ¬ p.Holds D t then h.choose else .top

private theorem separator_true (D : Model R M) {n : Nat} (s t : Tuple M n) :
    (separator D s t).Holds D s := by
  classical
  unfold separator
  split
  next h => exact h.choose_spec.1
  next => trivial

private theorem theory_of_separator (D : Model R M) {n : Nat} (s t : Tuple M n)
    (h : (separator D s t).Holds D t) : TheoryEq D s t := by
  classical
  have no : ¬ ∃ p : Formula R n, p.Holds D s ∧ ¬ p.Holds D t := by
    intro yes
    rw [separator, dif_pos yes] at h
    exact yes.choose_spec.2 h
  intro p
  constructor
  · exact fun hs => Classical.byContradiction fun hn => no ⟨p, hs, hn⟩
  · exact fun ht => Classical.byContradiction fun hn => no ⟨.neg p, hn, fun h => h ht⟩

noncomputable def label (C : Presentation R M) (D : Model R M) {n : Nat}
    (s : Tuple M n) : Formula R n := .conj fun i => separator D s (C.tuples n i)

theorem label_iff (C : Presentation R M) (D : Model R M) {n : Nat} (s t : Tuple M n) :
    (C.label D s).Holds D t ↔ TheoryEq D s t := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := C.tuples_onto t
    exact theory_of_separator D s t (hi ▸ h i)
  · intro h i
    exact (h _).mp (separator_true D s _)

theorem self_label (C : Presentation R M) (D : Model R M) {n : Nat} (s : Tuple M n) :
    (C.label D s).Holds D s := (C.label_iff D s s).mpr fun _ => Iff.rfl

noncomputable def atomicDiagram (C : Presentation R M) (D : Model R M) {n : Nat}
    (s : Tuple M n) : Formula R n := .conj fun i =>
  open Classical in
  match C.atoms n i with
  | none => .top
  | some a => if a.Holds D s then .atom a else .neg (.atom a)

theorem diagram_iff (C : Presentation R M) (D : Model R M) (E : Model R N) {n : Nat}
    (s : Tuple M n) (t : Tuple N n) :
    (C.atomicDiagram D s).Holds E t ↔ ∀ a : Atom R n, a.Holds D s ↔ a.Holds E t := by
  classical
  constructor
  · intro h a
    obtain ⟨i, hi⟩ := C.atoms_onto a
    specialize h i
    dsimp [atomicDiagram] at h
    rw [hi] at h
    by_cases ha : a.Holds D s <;> simp [ha, Formula.Holds] at h ⊢ <;> assumption
  · intro h i
    dsimp [atomicDiagram]
    cases hc : C.atoms n i with
    | none => trivial
    | some a =>
      by_cases ha : a.Holds D s
      · simp [ha, Formula.Holds, (h a).mp ha]
      · simp only [ha, ↓reduceIte, Formula.Holds]
        exact fun ht => ha ((h a).mpr ht)

/-- The two extension clauses for an individual tuple label. -/
noncomputable def extensions (C : Presentation R M) (D : Model R M) {n : Nat}
    (s : Tuple M n) : Formula R n :=
  Formula.and (.conj fun i => .ex (C.label D (push (C.enum i) s)))
    (.all (.disj fun i => C.label D (push (C.enum i) s)))

theorem extensions_iff (C : Presentation R M) (D : Model R M) (E : Model R N) {n : Nat}
    (s : Tuple M n) (t : Tuple N n) :
    (C.extensions D s).Holds E t ↔
      (∀ x : M, ∃ y : N, (C.label D (push x s)).Holds E (push y t)) ∧
      (∀ y : N, ∃ x : M, (C.label D (push x s)).Holds E (push y t)) := by
  simp only [extensions, Formula.holds_and, Formula.holds_all, Formula.holds_disj]
  constructor
  · rintro ⟨hf, hb⟩
    constructor
    · intro x; obtain ⟨i, rfl⟩ := C.onto x; exact hf i
    · intro y; obtain ⟨i, hi⟩ := hb y; exact ⟨C.enum i, hi⟩
  · rintro ⟨hf, hb⟩
    constructor
    · intro i; exact hf _
    · intro y; obtain ⟨x, hx⟩ := hb y; obtain ⟨i, rfl⟩ := C.onto x; exact ⟨i, hx⟩

noncomputable def localAxiom (C : Presentation R M) (D : Model R M) {n : Nat}
    (s : Tuple M n) : Formula R n :=
  (C.label D s).implies ((C.atomicDiagram D s).and (C.extensions D s))

noncomputable def sentence (C : Presentation R M) (D : Model R M) : Formula R 0 :=
  (C.label D (n := 0) Fin.elim0).and
    (.conj fun n => .conj fun i => (C.localAxiom D (C.tuples n i)).close)

theorem sentence_iff (C : Presentation R M) (D : Model R M) (E : Model R N) :
    BackAndForth.Satisfies E (C.sentence D) ↔
      (C.label D (n := 0) Fin.elim0).Holds E Fin.elim0 ∧
      ∀ {n} (s : Tuple M n) (t : Tuple N n), (C.localAxiom D s).Holds E t := by
  unfold sentence BackAndForth.Satisfies
  rw [Formula.holds_and]
  apply and_congr_right
  intro _
  constructor
  · intro h n s t
    obtain ⟨i, rfl⟩ := C.tuples_onto s
    exact (Formula.satisfies_close E _).mp (h n i) t
  · intro h n i
    exact (Formula.satisfies_close E _).mpr (h _)

theorem satisfies_self (C : Presentation R M) (D : Model R M) :
    BackAndForth.Satisfies D (C.sentence D) := by
  apply (C.sentence_iff D D).mpr
  refine ⟨C.self_label D _, ?_⟩
  intro n s t
  apply (Formula.holds_implies _ _ _ _).mpr
  intro ht
  have h := (C.label_iff D s t).mp ht
  apply (h _).mp
  apply (Formula.holds_and _ _ _ _).mpr
  refine ⟨(C.diagram_iff D D s s).mpr (fun _ => Iff.rfl), (C.extensions_iff D D s s).mpr ?_⟩
  exact ⟨fun x => ⟨x, C.self_label D _⟩, fun x => ⟨x, C.self_label D _⟩⟩

/-- A model of the displayed sentence has an explicit back-and-forth with the source. -/
noncomputable def system (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D)) : BackAndForth D E := by
  have ha := (C.sentence_iff D E).mp h
  have loc {n} {s : Tuple M n} {t : Tuple N n} (m : (C.label D s).Holds E t) :
      (∀ a : Atom R n, a.Holds D s ↔ a.Holds E t) ∧
      (∀ x : M, ∃ y : N, (C.label D (push x s)).Holds E (push y t)) ∧
      (∀ y : N, ∃ x : M, (C.label D (push x s)).Holds E (push y t)) := by
    have hlocal := (Formula.holds_implies _ _ _ _).mp (ha.2 s t) m
    have hh := (Formula.holds_and _ _ _ _).mp hlocal
    exact ⟨(C.diagram_iff D E s t).mp hh.1, (C.extensions_iff D E s t).mp hh.2⟩
  exact { matchTuples := fun s t => (C.label D s).Holds E t
          atoms := fun m => (loc m).1
          forth := fun m => (loc m).2.1
          back := fun m => (loc m).2.2 }

/-- Equivalence for arbitrary target cardinality. -/
theorem satisfies_iff_backAndForth (C : Presentation R M) (D : Model R M) (E : Model R N) :
    BackAndForth.Satisfies E (C.sentence D) ↔
      ∃ F : BackAndForth D E, F.matchTuples (n := 0) Fin.elim0 Fin.elim0 := by
  constructor
  · intro h
    exact ⟨C.system D E h, ((C.sentence_iff D E).mp h).1⟩
  · rintro ⟨F, h⟩
    exact (F.sentence_iff h _).mp (C.satisfies_self D)

end Presentation
end KnightModel.RankTwo.Scott
