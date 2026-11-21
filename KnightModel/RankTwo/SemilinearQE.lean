import KnightModel.RankTwo.Semilinear
import Mathlib.Algebra.Order.Field.Rat
import KnightModel.RankTwo.UnaryThreshold

/-! # Eliminating one vector variable by finite affine sampling -/

namespace KnightModel.RankTwo.Semilinear

open UnaryChoice

variable {V : Type*} {n : ℕ} [AddCommGroup V] [Module ℚ V] [LinearOrder V]
    [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V]

/-- The operations sampling a sign cell are affine, hence can be applied before
the remaining free vector variables have been evaluated. -/
structure AffineSamples {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V]
    (P : Samples V) where
  downOffset : V
  upOffset : V
  down_eq : ∀ x, P.down x = x + downOffset
  up_eq : ∀ x, P.up x = x + upOffset
  mid_eq : ∀ x y, P.mid x y = (2 : ℚ)⁻¹ • (x + y)

namespace Term

/-- If the head coefficient is nonzero this is the unique point of equality
in the head variable. A zero coefficient makes the inequality constant. -/
def cut (t : Term V (n+1)) : Term V n :=
  .scale t.slope⁻¹ (.scale (-1) t.residual)

theorem same_sign (t : Term V (n+1)) (p : Fin n → V) (x y : V)
    (h : (x < t.cut.eval p ↔ y < t.cut.eval p) ∧ (t.cut.eval p < x ↔ t.cut.eval p < y)) :
    t.eval (Fin.cons x p) < 0 ↔ t.eval (Fin.cons y p) < 0 := by
  rw [t.eval_cons x p, t.eval_cons y p]
  rcases lt_trichotomy t.slope 0 with hq | hq | hq
  · have eqcut : t.slope • t.cut.eval p = -t.residual.eval p := by
      simp [cut, eval, smul_smul, hq.ne]
    have neg (z : V) : t.slope • z + t.residual.eval p < 0 ↔ t.cut.eval p < z := by
      rw [← lt_neg_iff_add_neg, ← eqcut]
      exact (strictAnti_smul_left (β := V) hq).lt_iff_gt
    exact (neg x).trans (h.2.trans (neg y).symm)
  · simp [hq]
  · have eqcut : t.slope • t.cut.eval p = -t.residual.eval p := by
      simp [cut, eval, smul_smul, hq.ne']
    have pos (z : V) : t.slope • z + t.residual.eval p < 0 ↔ z < t.cut.eval p := by
      rw [← lt_neg_iff_add_neg, ← eqcut]
      exact (strictMono_smul_left_of_pos hq).lt_iff_lt
    exact (pos x).trans (h.1.trans (pos y).symm)

end Term

namespace Predicate

def cuts : Predicate V (n+1) → List (Term V n)
  | .ltZero t => [t.cut]
  | .neg f => f.cuts
  | .and f g => f.cuts ++ g.cuts

/-- With the other coordinates fixed, the formula depends only on the sign
cell of the first coordinate in the evaluated finite cut list. -/
theorem holds_sameCell (φ : Predicate V (n+1)) (p : Fin n → V) (x y : V)
    (h : SameCell (φ.cuts.map (·.eval p)) x y) :
    φ.Holds (Fin.cons x p) ↔ φ.Holds (Fin.cons y p) := by
  induction φ with
  | ltZero t => exact t.same_sign p x y (h _ (by simp [cuts]))
  | neg f ih => exact not_congr (ih h)
  | and f g ih jh =>
    apply and_congr
    · exact ih fun a ha => h a (by simp only [cuts, List.map_append]; exact List.mem_append_left _ ha)
    · exact jh fun a ha => h a (by simp only [cuts, List.map_append]; exact List.mem_append_right _ ha)

end Predicate

namespace AffineSamples

variable {P : Samples V}

/-- Finite candidates in the remaining variables, before evaluating the cuts. -/
def terms (A : AffineSamples P) (E : List (Term V n)) : List (Term V n) :=
  [.const P.base] ++ E ++ E.map (fun a => .add a (.const A.downOffset)) ++
    E.map (fun a => .add a (.const A.upOffset)) ++
    E.flatMap (fun a => E.map (fun b => .scale (2 : ℚ)⁻¹ (.add a b)))

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem eval_terms (A : AffineSamples P) (E : List (Term V n)) (p : Fin n → V) :
    (A.terms E).map (·.eval p) = samples P (E.map (·.eval p)) := by
  simp [terms, samples, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, Term.eval, A.down_eq, A.up_eq, A.mid_eq]

end AffineSamples

namespace Predicate

/-- A finite disjunction, compiled to the primitive Boolean operations. -/
def anyOf : List (Predicate V n) → Predicate V n
  | [] => .ltZero (.const 0)
  | x :: xs => x.disj (anyOf xs)

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem holds_anyOf (fs : List (Predicate V n)) (p : Fin n → V) :
    (anyOf fs).Holds p ↔ ∃ f ∈ fs, f.Holds p := by
  induction fs with
  | nil => simp [anyOf, Holds, Term.eval]
  | cons f fs ih => simp [anyOf, ih]

/-- Replace the first variable by an expression in the remaining variables. -/
def plug (φ : Predicate V (n+1)) (t : Term V n) : Predicate V n :=
  φ.subst (Fin.cons t (fun i => .var i))

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem holds_plug (φ : Predicate V (n+1)) (t : Term V n) (p : Fin n → V) :
    (φ.plug t).Holds p ↔ φ.Holds (Fin.cons (t.eval p) p) := by
  rw [plug, holds_subst]
  have e : (fun i => Term.eval (Fin.cons (α := fun _ : Fin (n+1) => Term V n) t Term.var i) p) = Fin.cons (t.eval p) p := by
    funext i
    cases i using Fin.cases <;> simp [Term.eval]
  rw [e]

/-- Single-variable quantifier elimination for Boolean combinations of strict
affine comparisons over an ordered rational vector space. -/
def existsHead {P : Samples V} (A : AffineSamples P) (φ : Predicate V (n+1)) : Predicate V n :=
  anyOf <| (A.terms φ.cuts).map φ.plug

theorem holds_existsHead {P : Samples V} (A : AffineSamples P) (φ : Predicate V (n+1))
    (p : Fin n → V) :
    (existsHead A φ).Holds p ↔ ∃ x : V, φ.Holds (Fin.cons x p) := by
  rw [existsHead, holds_anyOf]
  constructor
  · rintro ⟨_, h, hp⟩
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact ⟨_, (holds_plug φ t p).mp hp⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hc⟩ := exists_sample P (φ.cuts.map (·.eval p)) x
    rw [← A.eval_terms] at hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, (holds_plug φ t p).mpr ((φ.holds_sameCell p _ _ hc).mp hx)⟩

end Predicate

theorem Definable.exists_head {P : Samples V} (A : AffineSamples P)
    {S : Set (Fin (n+1) → V)} (h : Definable S) :
    Definable {p | ∃ x : V, Fin.cons x p ∈ S} := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.existsHead A, fun p => (exists_congr fun _ => hφ _).trans (φ.holds_existsHead A p).symm⟩

end KnightModel.RankTwo.Semilinear
