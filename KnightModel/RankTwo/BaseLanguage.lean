import KnightModel.RankTwo.Alphabet
import KnightModel.RankTwo.ScottIndex
import KnightModel.RankTwo.ScottLanguage
import Mathlib.Data.Rat.Encodable

/-!
# The named index and coefficient relations

Coefficients are named by rational numbers. The index functions, order, and
distinguished point use the existing pointed Knight language. These relations
recover each vector from its ordered finite support and rational coefficients.
-/

namespace KnightModel.RankTwo.Scott

inductive BaseRelation (Ω : Type) : Nat → Type where
  | index {n} (r : IndexRelation Ω n) : BaseRelation Ω n
  | indexSort : BaseRelation Ω 1
  | vectorSort : BaseRelation Ω 1
  | coefficient (q : ℚ) : BaseRelation Ω 2

variable {Ω I : Type} [Blueprint Ω] [KnightModel I Ω]

/-- The two base sorts. -/
abbrev BasePoints (I : Type) := I ⊕ VectorGroup I

def baseModel (i : I) : Model (BaseRelation Ω) (BasePoints I)
  | _, .index r, s => ∃ t, (∀ j, s j = .inl (t j)) ∧ indexModel i r t
  | _, .indexSort, s => ∃ x : I, s 0 = .inl x
  | _, .vectorSort, s => ∃ v : VectorGroup I, s 0 = .inr v
  | _, .coefficient q, s => ∃ (v : VectorGroup I) (x : I),
      s 0 = .inr v ∧ s 1 = .inl x ∧ v x = q

instance {Ω : Type} [Countable Ω] (n : Nat) : Countable (BaseRelation Ω n) := by
  classical
  let Enc := Unit ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ Ω ⊕ ℚ)))
  let decode : Enc → Σ k, BaseRelation Ω k
    | .inl _ => ⟨_, .index .mark⟩
    | .inr (.inl _) => ⟨_, .index .order⟩
    | .inr (.inr (.inl _)) => ⟨_, .indexSort⟩
    | .inr (.inr (.inr (.inl _))) => ⟨_, .vectorSort⟩
    | .inr (.inr (.inr (.inr (.inl c)))) => ⟨_, .index (.graph c)⟩
    | .inr (.inr (.inr (.inr (.inr q)))) => ⟨_, .coefficient q⟩
  have surj : Function.Surjective decode := by
    rintro ⟨k, r⟩
    cases r with
    | index r =>
      cases r with
      | mark => exact ⟨.inl (), rfl⟩
      | order => exact ⟨.inr (.inl ()), rfl⟩
      | graph c => exact ⟨.inr (.inr (.inr (.inr (.inl c)))), rfl⟩
    | indexSort => exact ⟨.inr (.inr (.inl ())), rfl⟩
    | vectorSort => exact ⟨.inr (.inr (.inr (.inl ()))), rfl⟩
    | coefficient q => exact ⟨.inr (.inr (.inr (.inr (.inr q)))), rfl⟩
  haveI : Countable (Σ k, BaseRelation Ω k) := surj.countable
  exact (show Function.Injective (Sigma.mk n : BaseRelation Ω n → Σ k, BaseRelation Ω k) from sigma_mk_injective).countable

end KnightModel.RankTwo.Scott
