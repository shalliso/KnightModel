import KnightModel.Transfinite.Seed
import Mathlib.Data.Sigma.Order

/-! # The language of a named countable ordered sum

Each component symbol is interpreted on tuples lying wholly in that
component. The order on the sum compares component numbers first.
-/

namespace KnightModel.Transfinite.NamedSum
open RankTwo.Scott

inductive Relation (R : ℕ → ℕ → Type) : ℕ → Type where
  | tag (i : ℕ) : Relation R 1
  | block (i : ℕ) {n} (r : R i n) : Relation R n
  | order : Relation R 2

instance {R : ℕ → ℕ → Type} [∀ i n, Countable (R i n)] (n : ℕ) : Countable (Relation R n) := by
  let decode : (ℕ ⊕ (Σ i, Σ n, R i n) ⊕ Unit) → Σ n, Relation R n
    | .inl i => ⟨1,.tag i⟩
    | .inr (.inl ⟨i,n,r⟩) => ⟨n,.block i r⟩
    | .inr (.inr _) => ⟨2,.order⟩
  have onto : Function.Surjective decode := by
    rintro ⟨_,r⟩
    cases r with
    | tag i => exact ⟨.inl i,rfl⟩
    | block i r => exact ⟨.inr (.inl ⟨i,_,r⟩),rfl⟩
    | order => exact ⟨.inr (.inr ()),rfl⟩
  haveI : Countable (Σ n, Relation R n) := onto.countable
  exact (show Function.Injective (Sigma.mk n : Relation R n → Σ n, Relation R n)
    from sigma_mk_injective).countable

abbrev Carrier (X : ℕ → Type) := Σₗ i, X i

def inject {X : ℕ → Type} (i : ℕ) (x : X i) : Carrier X := toLex ⟨i,x⟩
def tag {X : ℕ → Type} (v : Carrier X) : ℕ := (ofLex v).1

theorem inject_injective {X : ℕ → Type} (i : ℕ) : Function.Injective (@inject X i) :=
  fun _ _ e => sigma_mk_injective (congrArg ofLex e)

variable {R : ℕ → ℕ → Type} {X : ℕ → Type}

def Block (D : ∀ i, Model (R i) (X i)) {n} (i : ℕ) (r : R i n) (v : Tuple (Carrier X) n) : Prop :=
  ∃ t : Tuple (X i) n, (∀ l, v l = inject i (t l)) ∧ D i r t

def model (D : ∀ i, Model (R i) (X i)) (leSym : ∀ i, R i 2) : Model (Relation R) (Carrier X)
  | _, .tag i, v => tag (v 0) = i
  | _, .block i r, v => Block D i r v
  | _, .order, v => tag (v 0) < tag (v 1) ∨ ∃ i, Block D i (leSym i) v

@[simp] theorem onBlock (D : ∀ i, Model (R i) (X i)) {n} (i : ℕ) (r : R i n) (s : Tuple (X i) n) :
    Block D i r (inject i ∘ s) ↔ D i r s := by
  refine ⟨?_,fun h => ⟨s,fun _ => rfl,h⟩⟩
  rintro ⟨t,m,h⟩
  have eq : s = t := funext fun l => inject_injective i (m l)
  exact eq ▸ h

theorem order_iff [∀ i, LinearOrder (X i)] (D : ∀ i, Model (R i) (X i)) (leSym : ∀ i, R i 2)
    (le_ok : ∀ i (t : Tuple (X i) 2), D i (leSym i) t ↔ t 0 ≤ t 1) (v : Tuple (Carrier X) 2) :
    model D leSym .order v ↔ v 0 ≤ v 1 := by
  change (tag (v 0) < tag (v 1) ∨ ∃ i, Block D i (leSym i) v) ↔ _
  constructor
  · rintro (cross | ⟨i,t,inc,h⟩)
    · exact Sigma.Lex.le_def.mpr (.inl cross)
    · rw [inc 0, inc 1]
      exact Sigma.Lex.right _ _ ((le_ok i t).mp h)
  · intro h
    rcases Sigma.Lex.le_def.mp h with cross | ⟨eq,rel⟩
    · exact .inl cross
    · right
      let j := tag (v 1)
      let x : X j := @Eq.rec _ _ (fun k _ => X k) (ofLex (v 0)).2 _ eq
      let y : X j := (ofLex (v 1)).2
      let t : Tuple (X j) 2 := Fin.cases x (fun _ => y)
      refine ⟨j,t,Fin.cases ?_ (Fin.cases rfl (fun i => i.elim0)),(le_ok j t).mpr rel⟩
      apply congrArg toLex
      exact Sigma.ext eq (by exact eqRec_heq _ _ |>.symm)

end KnightModel.Transfinite.NamedSum
