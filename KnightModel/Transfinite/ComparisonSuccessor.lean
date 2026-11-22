import KnightModel.Transfinite.Comparison
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-! # Raising a uniform finite-tuple comparison bound

The hypothesis records exactly what a canonical parameter provides: inside
the stabilizer of the higher tuple, a finite tuple in the old sort has the same
stabilizer as the lower tuple. Codes for individual entries concatenate.
-/

namespace KnightModel.Transfinite

universe w

variable {G O X : Type*} [Group G] [MulAction G X] [MulAction G O]

/-- A finite tuple in the indicated sort has the same stabilizer as the point
within the subgroup in question. -/
def CodedBy (H : Subgroup G) (O : Type*) [MulAction G O] (x : X) : Prop :=
  ∃ n : ℕ, ∃ p : Fin n → O, ∀ g ∈ H, g • p = p ↔ g • x = x

theorem CodedBy.restrict {H J : Subgroup G} {x : X} (h : H ≤ J)
    (code : CodedBy J O x) : CodedBy H O x := by
  obtain ⟨n, p, hp⟩ := code
  exact ⟨n, p, fun g hg => hp g (h hg)⟩

theorem tuple_fixed_iff {m : ℕ} (g : G) (x : Fin m → X) :
    g • x = x ↔ ∀ i, g • (x i) = x i :=
  funext_iff

private theorem fixed_append {m n : ℕ} (g : G) (p : Fin m → O) (q : Fin n → O) :
    g • (Fin.append p q) = Fin.append p q ↔ g • p = p ∧ g • q = q := by
  simp only [tuple_fixed_iff]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (i.castAdd n), fun j => by simpa using h (j.natAdd m)⟩
  · rintro ⟨hp, hq⟩
    exact Fin.addCases (fun i => by simpa using hp i) (fun j => by simpa using hq j)

/-- Turn pointwise fixing of an unordered support into an ordered tuple code. -/
theorem CodedBy.of_finset {H : Subgroup G} {x : X} (s : Finset O)
    (fix : ∀ g ∈ H, g • x = x ↔ ∀ i ∈ s, g • i = i) : CodedBy H O x := by
  classical
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i).1, fun g hg => ?_⟩
  rw [tuple_fixed_iff, fix g hg]
  exact ⟨fun h i hi => by simpa using h (e ⟨i, hi⟩), fun h i => h _ (e.symm i).2⟩

/-- All entries may use different code lengths, including zero. -/
theorem CodedBy.tuple {H : Subgroup G} {m : ℕ} {x : Fin m → X}
    (codes : ∀ i, CodedBy H O (x i)) : CodedBy H O x := by
  induction m with
  | zero =>
    exact ⟨0, Fin.elim0, fun _ _ => ⟨fun _ => Subsingleton.elim .., fun _ => Subsingleton.elim ..⟩⟩
  | succ m ih =>
    obtain ⟨n, p, hp⟩ := codes 0
    obtain ⟨k, q, hq⟩ := ih (x := Fin.tail x) (fun i => codes i.succ)
    refine ⟨n+k, Fin.append p q, fun g hg => ?_⟩
    rw [fixed_append, hp g hg, hq g hg, tuple_fixed_iff g x, Fin.forall_fin_succ, tuple_fixed_iff]
    rfl

/-- A strict old tuple bound yields a strict bound for every coded point. -/
theorem CodedBy.comparisonLT {α : Ordinal.{w}} {H J : Subgroup G} {x : X}
    (code : CodedBy H O x) (sub : H ≤ J)
    (old : ∀ n (p : Fin n → O), ComparisonLT α J p) : ComparisonLT α H x := by
  obtain ⟨n, p, hp⟩ := code
  obtain ⟨β, hb, hr⟩ := old n p
  exact ⟨β, hb, (hr.restrict sub).of_stabilizer hp⟩

/-- If one of two conjugate objects is coded over the other, comparison
raises a strict bound on old tuples to a weak bound on the new object.
The object may itself have arbitrary finite arity. -/
theorem comparisonLE_of_coded_conjugates {α : Ordinal.{w}} (hα : α ≠ 0)
    {H : Subgroup G} {x : X} (old : ∀ n (p : Fin n → O), ComparisonLT α H p)
    (code : ∀ g ∈ H, CodedBy (H ⊓ MulAction.stabilizer G (g • x)) O x ∨
      CodedBy (H ⊓ MulAction.stabilizer G x) O (g • x)) : ComparisonLE α H x := by
  apply (comparisonLE_iff_of_ne_zero hα ..).2
  exact fun g hg => (code g hg).imp
    (fun c => c.comparisonLT inf_le_left old) (fun c => c.comparisonLT inf_le_left old)

/-- Coordinatewise codes over whichever conjugate has the higher endpoint
suffice uniformly in arity. -/
theorem comparisonLE_tuple_of_coded_conjugates {α : Ordinal.{w}} (hα : α ≠ 0)
    {H : Subgroup G} (old : ∀ n (p : Fin n → O), ComparisonLT α H p) {m : ℕ}
    (x : Fin m → X) (code : ∀ g ∈ H,
      (∀ i, CodedBy (H ⊓ MulAction.stabilizer G (g • x)) O (x i)) ∨
      (∀ i, CodedBy (H ⊓ MulAction.stabilizer G x) O ((g • x) i))) :
    ComparisonLE α H x :=
  comparisonLE_of_coded_conjugates hα old fun g hg => (code g hg).imp CodedBy.tuple CodedBy.tuple

end KnightModel.Transfinite
