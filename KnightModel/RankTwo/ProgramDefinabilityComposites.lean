import KnightModel.RankTwo.ProgramDefinabilityScheme
import KnightModel.RankTwo.WordBounds
import KnightModel.RankTwo.WordScalar

/-! # Inversion, composition and union of concrete named schemes -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I]
variable (i : I)

theorem concrete_graph_bound {n} (k : Name n) (v : Fin n → VectorGroup I) :
    PrefixBounds (schemeGraph i k v) k.val.graphBound :=
  schemeGraph_bounds i k _ (fun t => WordScheme.prefixBounds _ _ _ _ _ _ _ (by simp [k.property])) v

private abbrev Raw (c : WordScheme) := schemeGraph i (⟨c,rfl⟩ : Name c.arity)

private theorem def_param_guard {n} {R : (Fin n → VectorGroup I) → List (Letter I) → List (Letter I) → Prop}
    (h : LiftDefinable Subtype.val R) :
    LiftDefinable Subtype.val (fun p x y => (∀ j, 0 ≤ p j) ∧ R p x y) := by
  intro m s x y
  have good : Definable {p | ∀ j, 0 ≤ evalTuple s p j} := by
    convert def_word_nonneg (List.ofFn s) using 1
    ext p
    change (∀ j, 0 ≤ (s j).eval p) ↔ ∀ a ∈ evalWord (List.ofFn s) p, 0 ≤ a
    simp [evalWord,List.mem_ofFn]
  convert good.inter (h s x y) using 1
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,valid,r⟩
    exact ⟨valid,a,b,ha,hb,r⟩
  · rintro ⟨valid,a,b,ha,hb,r⟩
    exact ⟨a,b,ha,hb,valid,r⟩

private theorem guard_ext {k : WordScheme}
    (F : (Fin k.arity → VectorGroup I) → List (Letter I) → List (Letter I) → Prop)
    (agree : ∀ (t : Fin k.arity → Letter I) x y, F (fun j => (t j).val) x y ↔
      k.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter (List.ofFn t) x y)
    (p : Fin k.arity → VectorGroup I) (x y : List (Letter I)) :
    ((∀ j, 0 ≤ p j) ∧ F p x y) ↔ Raw i k p x y := by
  constructor
  · rintro ⟨valid,h⟩
    let t (j : Fin k.arity) : Letter I := ⟨p j,valid j⟩
    exact ⟨t,fun _ => rfl,(agree t x y).mp h⟩
  · rintro ⟨t,ht,h⟩
    obtain rfl : p = fun j => (t j).val := funext fun j => (ht j).symm
    exact ⟨fun j => (t j).property,(agree t x y).mpr h⟩

private abbrev leftArgs {A : Type*} {m n : Nat} (p : Fin (m+n) → A) (j : Fin m) : A := p (j.castAdd n)
private abbrev rightArgs {A : Type*} {m n : Nat} (p : Fin (m+n) → A) (j : Fin n) : A := p (j.natAdd m)

private theorem take_args {A : Type*} {m n : Nat} (p : Fin (m+n) → A) :
    (List.ofFn p).take m = List.ofFn (leftArgs p) := by
  rw [List.ofFn_add]
  exact List.take_left' (by simp)

private theorem drop_args {A : Type*} {m n : Nat} (p : Fin (m+n) → A) :
    (List.ofFn p).drop m = List.ofFn (rightArgs p) := by
  rw [List.ofFn_add]
  exact List.drop_left' (by simp)

private theorem left_def {f g : WordScheme} (h : SchemeDefinable i f) :
    LiftDefinable Subtype.val (fun p : Fin (f.arity+g.arity) → VectorGroup I => Raw i f (leftArgs p)) :=
  LiftDefinable.parameters (R := Raw i f) h (fun j => .var (j.castAdd g.arity))

private theorem right_def {f g : WordScheme} (h : SchemeDefinable i g) :
    LiftDefinable Subtype.val (fun p : Fin (f.arity+g.arity) → VectorGroup I => Raw i g (rightArgs p)) :=
  LiftDefinable.parameters (R := Raw i g) h (fun j => .var (j.natAdd f.arity))

private theorem rel_congr (f : WordScheme) {p q : List (Letter I)} (hp : p = q) (x y : List (Letter I)) :
    f.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter p x y ↔
    f.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter q x y :=
  hp ▸ Iff.rfl

namespace SchemeDefinable

theorem inv {f : WordScheme} (h : SchemeDefinable i f) : SchemeDefinable i (.inv f) := by
  apply LiftDefinable.congr (R := fun p x y => Raw i f p y x) (LiftDefinable.inv (R := Raw i f) h)
  intro p x y
  rfl

theorem union {f g : WordScheme} (h : SchemeDefinable i f) (k : SchemeDefinable i g) :
    SchemeDefinable i (.union f g) := by
  let F := fun (p : Fin (f.arity+g.arity) → VectorGroup I) x y =>
    Raw i f (leftArgs p) x y ∨ Raw i g (rightArgs p) x y
  have hd : LiftDefinable Subtype.val F := LiftDefinable.union
    (R := fun p : Fin (f.arity+g.arity) → VectorGroup I => Raw i f (leftArgs p))
    (S := fun p => Raw i g (rightArgs p)) (left_def i h) (right_def i k)
  apply LiftDefinable.congr (R := fun p x y => (∀ j, 0 ≤ p j) ∧ F p x y) (def_param_guard hd)
  apply guard_ext i (k := .union f g) F
  intro t x y
  change Raw i f (fun j => (leftArgs t j).val) x y ∨ Raw i g (fun j => (rightArgs t j).val) x y ↔ _
  simp only [Raw, schemeGraph_letters, WordScheme.Rel]
  exact or_congr (rel_congr i f (take_args (m := f.arity) (n := g.arity) t).symm x y)
    (rel_congr i g (drop_args (m := f.arity) (n := g.arity) t).symm x y)

theorem seq {f g : WordScheme} (h : SchemeDefinable i f) (k : SchemeDefinable i g) :
    SchemeDefinable i (.seq f g) := by
  let L := fun (p : Fin (f.arity+g.arity) → VectorGroup I) => Raw i f (leftArgs p)
  let M := fun (p : Fin (f.arity+g.arity) → VectorGroup I) => Raw i g (rightArgs p)
  let F := fun p x y => ∃ z, L p x z ∧ M p z y
  have hd : LiftDefinable Subtype.val F := LiftDefinable.seq
    (R := L) (S := M) (Definable.exists_head (vectorAffineSamples i)) Subtype.val_injective
    (left_def i h) (right_def i k) f.graphBound (fun p => concrete_graph_bound i ⟨f,rfl⟩ (leftArgs p))
  apply LiftDefinable.congr (R := fun p x y => (∀ j, 0 ≤ p j) ∧ F p x y) (def_param_guard hd)
  apply guard_ext i (k := .seq f g) F
  intro t x y
  change (∃ z, Raw i f (fun j => (leftArgs t j).val) x z ∧ Raw i g (fun j => (rightArgs t j).val) z y) ↔ _
  simp only [Raw, schemeGraph_letters, WordScheme.Rel]
  exact exists_congr fun z => and_congr (rel_congr i f (take_args (m := f.arity) (n := g.arity) t).symm x z)
    (rel_congr i g (drop_args (m := f.arity) (n := g.arity) t).symm z y)

end SchemeDefinable
end KnightModel.RankTwo.Concrete
