import KnightModel.RankTwo.Semilinear
import KnightModel.RankTwo.ProgramDefinability

/-! # Semilinearity of equality fibers of parameterized word graphs -/

namespace KnightModel.RankTwo.Semilinear

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V]

abbrev HeadElimination (V : Type*) [AddCommGroup V] [Module ℚ V] [LinearOrder V] :=
  ∀ {n} {S : Set (Fin (n+1) → V)}, Definable S → Definable {p | ∃ z, Fin.cons z p ∈ S}

def evalWord {n} (w : List (Term V n)) (p : Fin n → V) : List V := w.map (·.eval p)

abbrev evalTuple {n m} (s : Fin n → Term V m) (p : Fin m → V) : Fin n → V := fun i => (s i).eval p

/-- A fixed pair of symbolic word lengths and a symbolic parameter tuple give
a semilinear evaluation predicate. -/
def GraphDefinable {n} (R : (Fin n → V) → List V → List V → Prop) : Prop :=
  ∀ {k} (s : Fin n → Term V k) (x y : List (Term V k)),
    Definable {p | R (evalTuple s p) (evalWord x p) (evalWord y p)}

theorem bounded_exists (qe : HeadElimination V) (bound : Nat)
    {n} (Q : (Fin n → V) → List V → Prop)
    (defQ : ∀ {k} (s : Fin n → Term V k) (w : List (Term V k)),
      Definable {p | Q (evalTuple s p) (evalWord w p)}) :
    Definable {p | ∃ w, w.length ≤ bound ∧ Q p w} := by
  induction bound generalizing n with
  | zero =>
    convert defQ (Term.var ·) [] using 1
    ext p
    simp [evalWord]
    rfl
  | succ b ih =>
    let Q' (p : Fin (n+1) → V) (w : List V) := Q (Fin.tail p) (p 0 :: w)
    have hd : Definable {p | ∃ w, w.length ≤ b ∧ Q' p w} :=
      ih Q' (fun s w => defQ (Fin.tail s) (s 0 :: w))
    have hex := qe hd
    have hnil := defQ (Term.var ·) []
    convert hnil.union hex using 1
    ext p
    change (∃ w : List V, w.length ≤ b+1 ∧ Q p w) ↔
      Q p [] ∨ ∃ (a : V) (w : List V), w.length ≤ b ∧ Q' (Fin.cons a p) w
    simp only [Q', Fin.tail_cons, Fin.cons_zero]
    constructor
    · rintro ⟨w, hlen, hQ⟩
      cases w with
      | nil => exact Or.inl hQ
      | cons a w => exact Or.inr ⟨a,w,by simpa using hlen,hQ⟩
    · rintro (h | ⟨a,w,hw,h⟩)
      · exact ⟨[], Nat.zero_le _, h⟩
      · exact ⟨a :: w, by simpa using hw, h⟩

private theorem def_not {n} {P : (Fin n → V) → Prop} (h : Definable {x | P x}) :
    Definable {x | ¬ P x} := h.compl

private theorem def_and {n} {P Q : (Fin n → V) → Prop}
    (h : Definable {x | P x}) (g : Definable {x | Q x}) : Definable {x | P x ∧ Q x} := h.inter g

private theorem def_or {n} {P Q : (Fin n → V) → Prop}
    (h : Definable {x | P x}) (g : Definable {x | Q x}) : Definable {x | P x ∨ Q x} := h.union g

private theorem def_iff {n} {P Q : (Fin n → V) → Prop}
    (h : Definable {x | P x}) (g : Definable {x | Q x}) : Definable {x | P x ↔ Q x} := by
  convert def_or (def_and h g) (def_and (def_not h) (def_not g)) using 1
  ext x
  change (P x ↔ Q x) ↔ ((P x ∧ Q x) ∨ (¬P x ∧ ¬Q x))
  tauto

theorem bounded_all (qe : HeadElimination V) (bound : Nat)
    {n} (Q : (Fin n → V) → List V → Prop)
    (defQ : ∀ {k} (s : Fin n → Term V k) (w : List (Term V k)),
      Definable {p | Q (evalTuple s p) (evalWord w p)}) :
    Definable {p | ∀ w, w.length ≤ bound → Q p w} := by
  convert def_not (bounded_exists qe bound (fun p w => ¬ Q p w)
    (fun s w => def_not (defQ s w))) using 1
  ext p
  simp

omit [LinearOrder V] in
theorem eval_subst_word {n k} (w : List (Term V n)) (s : Fin n → Term V k) (p : Fin k → V) :
    evalWord (w.map (·.subst s)) p = evalWord w (evalTuple s p) := by
  simp [evalWord, List.map_map, Function.comp_def]

omit [LinearOrder V] in
@[simp] theorem eval_subst_tuple {m n k} (s : Fin n → Term V m) (t : Fin m → Term V k)
    (p : Fin k → V) : evalTuple (fun i => (s i).subst t) p = evalTuple s (evalTuple t p) := by
  funext i
  exact Term.eval_subst t _ _

omit [LinearOrder V] in
@[simp] theorem eval_const_tuple {m k} (q : Fin m → V) (p : Fin k → V) :
    evalTuple (fun i => Term.const (q i)) p = q := rfl

namespace GraphDefinable

variable {n} {R S : (Fin n → V) → List V → List V → Prop}

theorem inv (h : GraphDefinable R) : GraphDefinable (fun p x y => R p y x) := fun s x y => h s y x

theorem union (h : GraphDefinable R) (g : GraphDefinable S) :
    GraphDefinable (fun p x y => R p x y ∨ S p x y) := fun s x y => def_or (h s x y) (g s x y)

/-- In relational composition the bound on the first operation makes the
intermediate word quantifier a finite family of ordinary vector quantifiers. -/
theorem seq_of_length (qe : HeadElimination V) (h : GraphDefinable R) (g : GraphDefinable S)
    (b : Nat) (bound : ∀ p x z, R p x z → z.length ≤ x.length + b) :
    GraphDefinable (fun p x y => ∃ z, R p x z ∧ S p z y) := by
  intro k s x y
  let Q (p : Fin k → V) (z : List V) := R (evalTuple s p) (evalWord x p) z ∧
    S (evalTuple s p) z (evalWord y p)
  have hd := bounded_exists qe (x.length+b) Q (fun t z => by
    have a := h (fun i => (s i).subst t) (x.map (·.subst t)) z
    have c := g (fun i => (s i).subst t) z (y.map (·.subst t))
    simpa only [Q, eval_subst_tuple, eval_subst_word] using def_and a c)
  convert hd using 1
  ext p
  change (∃ z, Q p z) ↔ ∃ z, z.length ≤ x.length+b ∧ Q p z
  refine ⟨fun ⟨z, hz⟩ => ⟨z, ?_, hz⟩, fun ⟨z,_,hz⟩ => ⟨z,hz⟩⟩
  simpa [evalWord] using bound _ _ _ hz.1

theorem seq (qe : HeadElimination V) (h : GraphDefinable R) (g : GraphDefinable S)
    (b : Nat) (bound : ∀ p, PrefixBounds (R p) b) :
    GraphDefinable (fun p x y => ∃ z, R p x z ∧ S p z y) :=
  seq_of_length qe h g b (fun p _ _ hr => ((bound p).sizes hr).2)

/-- If the two whole graphs agree exactly when their bounded tests agree,
the fiber of parameters presenting the fixed right-hand graph is semilinear.
This also applies when the finite tests reject inputs outside the alphabet. -/
theorem equality_fiber_of_test {m}
    {T : (Fin m → V) → List V → List V → Prop}
    (qe : HeadElimination V) (h : GraphDefinable R) (g : GraphDefinable T)
    (q : Fin m → V) (b : Nat) (equal : (Fin n → V) → Prop)
    (test : ∀ p, equal p ↔
      ∀ x y, x.length ≤ b → y.length ≤ b → (R p x y ↔ T q x y)) :
    Definable {p | equal p} := by
  let Q (p : Fin n → V) (x : List V) := ∀ y, y.length ≤ b → (R p x y ↔ T q x y)
  have hd := bounded_all qe b Q (fun s x => by
    apply bounded_all qe b
    intro k t y
    have a := h (fun i => (s i).subst t) (x.map (·.subst t)) y
    have c := g (fun i => .const (q i)) (x.map (·.subst t)) y
    simpa only [eval_subst_tuple, eval_const_tuple, eval_subst_word] using def_iff a c)
  convert hd using 1
  ext p
  change equal p ↔ ∀ x, x.length ≤ b → ∀ y, y.length ≤ b → (R p x y ↔ T q x y)
  rw [test]
  constructor <;> intro a x b' c d
  · exact a x c b' d
  · exact a x c b' d

/-- Uniformly bounded prefix relations have semilinear fibers of parameters
defining any fixed graph of another such scheme. -/
theorem equality_fiber {m} {T : (Fin m → V) → List V → List V → Prop}
    (qe : HeadElimination V) (h : GraphDefinable R) (g : GraphDefinable T)
    (q : Fin m → V) (a b : Nat)
    (hr : ∀ p, PrefixBounds (R p) a) (ht : PrefixBounds (T q) b) :
    Definable {p | ∀ x y, R p x y ↔ T q x y} :=
  equality_fiber_of_test qe h g q (2 * max a b) _
    (fun p => ((hr p).mono (Nat.le_max_left ..)).ext_iff (ht.mono (Nat.le_max_right ..)))

end GraphDefinable
end KnightModel.RankTwo.Semilinear
