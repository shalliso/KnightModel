import KnightModel.RankTwo.Amalgamation
import KnightModel.RankTwo.ScottRestrictionLabels

/-! # Pair labels read the profiles of orbital terms in an actual Scott amalgam -/

namespace KnightModel.RankTwo.Scott

namespace Formula

variable {R : Nat → Type u} {M : Type v}

private def liftVars {n m} (f : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (f i).succ)

/-- Rename the free variables of a countable infinitary formula. -/
def pull {n} (p : Formula R n) : {m : Nat} → (Fin n → Fin m) → Formula R m :=
  match p with
  | .top => fun _ => .top
  | .atom (.eq i j) => fun f => .atom (.eq (f i) (f j))
  | .atom (.rel r args) => fun f => .atom (.rel r (f ∘ args))
  | .neg q => fun f => .neg (q.pull f)
  | .conj φ => fun f => .conj (fun i => (φ i).pull f)
  | .ex q => fun f => .ex (q.pull (liftVars f))

@[simp] theorem holds_pull (D : Model R M) {n} (p : Formula R n) {m}
    (f : Fin n → Fin m) (t : Tuple M m) : (p.pull f).Holds D t ↔ p.Holds D (t ∘ f) := by
  induction p generalizing m with
  | top => rfl
  | atom a => cases a <;> rfl
  | neg p ih => exact not_congr (ih f t)
  | conj ps ih => exact forall_congr' fun i => ih i f t
  | ex p ih =>
    apply exists_congr
    intro x
    have e : push x t ∘ liftVars f = push x (t ∘ f) := funext (Fin.cases rfl (fun _ => rfl))
    exact (ih (liftVars f) (push x t)).trans (e ▸ Iff.rfl)

end Formula

namespace MarkedExtension

open Amalgamation

variable {R : Nat → Type} {M D N P X : Type} {k : Nat}

private def skipSecond {n} : Fin (n+1) → Fin (n+2) := Fin.cases 0 (fun i => i.succ.succ)

private theorem skipSecond_push {n} (x y : N) (t : Tuple N n) :
    push x (push y t) ∘ skipSecond = push x t := funext (Fin.cases rfl (fun _ => rfl))

private theorem push_map {n} (f : D → N) (x : D) (t : Tuple D n) :
    f ∘ push x t = push (f x) (f ∘ t) := funext (Fin.cases rfl (fun _ => rfl))

/-- Infinitary-elementary embedding between two models. -/
structure Elementary (D₀ : Model R D) (E : Model R N) extends D ↪ N where
  truth : ∀ {n} (φ : Formula R n) (t : Tuple D n), φ.Holds D₀ t ↔ φ.Holds E (toFun ∘ t)

instance {D₀ : Model R D} {E : Model R N} : CoeFun (Elementary D₀ E) (fun _ => D → N) :=
  ⟨fun f => f.toFun⟩

/-- Finite old parameters, one new point, and the orbital functions recovering
the old points in its relative orbit. Each function is supplied as its graph formula. -/
structure Terms (D₀ : Model R D) (P : Type) (k : Nat) where
  base : Tuple D k
  mark : D
  values : P ↪ D
  graph : P → Formula R (k+2)
  unique : ∀ i z, (graph i).Holds D₀ (push z (push mark base)) ↔ z = values i

private def atMostOne (φ : Formula R (k+1)) : Formula R (k+1) :=
  .all ((φ.pull skipSecond).implies (.atom (.eq 0 1)))

private theorem holds_atMostOne (D₀ : Model R D) (φ : Formula R (k+1)) (t : Tuple D k) (v : D) :
    (atMostOne φ).Holds D₀ (push v t) ↔ ∀ z, φ.Holds D₀ (push z t) → z = v := by
  simp only [atMostOne,Formula.holds_all,Formula.holds_implies,Formula.holds_pull,skipSecond_push]
  rfl

/-- Unique values of an orbital graph remain unique in an elementary extension,
including when there are additional prospective outputs in the larger carrier. -/
theorem Elementary.unique_fiber {D₀ : Model R D} {E : Model R N} (f : Elementary D₀ E)
    (φ : Formula R (k+1)) (b : Tuple D k) (v : D)
    (unique : ∀ z, φ.Holds D₀ (push z b) ↔ z = v) (z : N) :
    φ.Holds E (push z (f ∘ b)) ↔ z = f v := by
  have hv := (f.truth φ _).mp ((unique v).mpr rfl)
  rw [push_map] at hv
  have hs := (holds_atMostOne D₀ φ b v).mpr (fun z h => (unique z).mp h)
  have ht := (f.truth (atMostOne φ) _).mp hs
  rw [push_map] at ht
  exact ⟨(holds_atMostOne E _ _ _).mp ht z,fun e => e ▸ hv⟩

theorem Terms.elementary_fiber {D₀ : Model R D} {E : Model R N}
    (T : Terms D₀ P k) (f : Elementary D₀ E) (i : P) (z : N) :
    (T.graph i).Holds E (push z (push (f T.mark) (f ∘ T.base))) ↔ z = f (T.values i) := by
  simpa only [push_map] using f.unique_fiber (T.graph i) (push T.mark T.base) (T.values i) (T.unique i) z

private def common (θ ψ : Formula R (k+2)) : Formula R (k+2) :=
  .ex ((θ.pull skipSecond).and (ψ.pull (Fin.cases 0 (fun i => (skipSecond i).succ))))

private theorem holds_common (E : Model R N) (θ ψ : Formula R (k+2))
    (x y : N) (b : Tuple N k) :
    (common θ ψ).Holds E (push y (push x b)) ↔
      ∃ z, θ.Holds E (push z (push x b)) ∧ ψ.Holds E (push z (push y b)) := by
  refine exists_congr fun z => ?_
  simp only [Formula.holds_and,Formula.holds_pull,skipSecond_push]
  have eqv : push z (push y (push x b)) ∘ (Fin.cases 0 (fun i => (skipSecond i).succ)) =
      push z (push y b) := funext (Fin.cases rfl (fun i => congrFun (skipSecond_push y x b) i))
  rw [eqv]

/-- Actual amalgamation of two copies of the same extension. Only the equations
on the shared old points and the finite base are used, so extra identifications are allowed. -/
structure CommonModel (C : Presentation R M) (S : Model R M) {D₀ : Model R D} (T : Terms D₀ P k)
    (s t : Equiv.Perm P) (N : Type) where
  model : Model R N
  sentence : BackAndForth.Satisfies model (C.sentence S)
  left : Elementary D₀ model
  right : Elementary D₀ model
  base_eq : left ∘ T.base = right ∘ T.base
  shared : P ↪ N
  left_values : ∀ i, left (T.values i) = shared (s i)
  right_values : ∀ i, right (T.values i) = shared (t i)

def Compatible (C : Presentation R M) (S : Model R M) {D₀ : Model R D} (T : Terms D₀ P k)
    (s t : Equiv.Perm P) : Prop := ∃ N : Type, Nonempty (CommonModel C S T s t N)

private def table (C : Presentation R M) (S : Model R M) {D₀ : Model R D}
    (T : Terms D₀ P k) (l : Nat) (i j : P) :=
  (common (T.graph i) (T.graph j)).Holds S (C.tuples (k+2) l)

theorem pair_label {C : Presentation R M} {S : Model R M} {D₀ : Model R D}
    {T : Terms D₀ P k} {s t : Equiv.Perm P} (h : Compatible C S T s t) :
    ∃ l, Records (table C S T) l s t := by
  obtain ⟨N,⟨E⟩⟩ := h
  let b := E.left ∘ T.base
  let pair := push (E.right T.mark) (push (E.left T.mark) b)
  let l := SentenceLabels.number C S E.model E.sentence pair
  refine ⟨l,fun i j => ?_⟩
  have q := (C.system S E.model E.sentence).holds_iff (s := C.tuples (k+2) l) (t := pair) (common (T.graph i) (T.graph j))
    (SentenceLabels.number_spec C S E.model E.sentence pair)
  refine q.trans ((holds_common E.model _ _ _ _ _).trans ?_)
  change (∃ z, (T.graph i).Holds E.model (push z (push (E.left T.mark) (E.left ∘ T.base))) ∧
      (T.graph j).Holds E.model (push z (push (E.right T.mark) (E.left ∘ T.base)))) ↔ _
  simp_rw [T.elementary_fiber E.left, E.base_eq, T.elementary_fiber E.right]
  simp [E.left_values,E.right_values]

theorem compatible_symm {C : Presentation R M} {S : Model R M} {D₀ : Model R D}
    {T : Terms D₀ P k} {s t : Equiv.Perm P} (h : Compatible C S T s t) : Compatible C S T t s := by
  obtain ⟨N,⟨E⟩⟩ := h
  exact ⟨N,⟨{
    model := E.model
    sentence := E.sentence
    left := E.right
    right := E.left
    base_eq := E.base_eq.symm
    shared := E.shared
    left_values := E.right_values
    right_values := E.left_values }⟩⟩

open Cardinal

theorem incompatible_twists (C : Presentation R M) (S : Model R M) {D₀ : Model R D}
    (T : Terms D₀ P k) (twist : X ↪ Equiv.Perm P) (size : #X = 2 ^ ℵ₀) :
    ∃ F : Set X, #F = 2 ^ ℵ₀ ∧ F.Pairwise (fun a b => ¬ Compatible C S T (twist a) (twist b)) :=
  continuum_incompatible twist _ (table C S T) (fun _ _ => pair_label)
    (fun _ _ => compatible_symm) size

end MarkedExtension
end KnightModel.RankTwo.Scott
