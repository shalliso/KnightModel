import KnightModel.RankTwo.ScottIso
import Mathlib.Data.Countable.Basic

/-! # Countable relational languages and countable presentations -/

namespace KnightModel.RankTwo.Scott

universe u v
local instance (n : Nat) : Finite (Fin n) := .intro (Equiv.refl _)

instance {R : Nat → Type u} [∀ k, Countable (R k)] (n : Nat) : Countable (Atom R n) := by
  let make : (Fin n × Fin n) ⊕ (Σ k, R k × (Fin k → Fin n)) → Atom R n :=
    fun | .inl (i,j) => .eq i j | .inr ⟨_, r, s⟩ => .rel r s
  have onto : Function.Surjective make := by
    intro a
    cases a with
    | eq i j => exact ⟨.inl (i,j), rfl⟩
    | rel r s => exact ⟨.inr ⟨_, r, s⟩, rfl⟩
  exact onto.countable

/-- A countable language and a nonempty countable carrier supply all enumerations
needed by the syntactic Scott construction. -/
noncomputable def Presentation.ofCountable (R : Nat → Type u) (M : Type v)
    [∀ k, Countable (R k)] [Nonempty M] [Countable M] : Presentation R M where
  enum := (exists_surjective_nat M).choose
  onto := (exists_surjective_nat M).choose_spec
  tuples n := (exists_surjective_nat (Tuple M n)).choose
  tuples_onto {n} := (exists_surjective_nat (Tuple M n)).choose_spec
  atoms n := (exists_surjective_nat (Option (Atom R n))).choose
  atoms_onto {n} a := (exists_surjective_nat (Option (Atom R n))).choose_spec (some a)

end KnightModel.RankTwo.Scott
