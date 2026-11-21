/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import KnightModel.RankTwo.ScottSentence

/-!
# Moving the anchor in a back-and-forth on frames

A coordinate is a whole-domain chart onto an initial interval. Frames carry their
right action. Two proper coordinates differ on the left by a change of coordinates:
geometrically one pastes the isomorphism of the initial intervals to an isomorphism
of their complementary tails. The upward move below uses this pasting law on the
target only. The extra change of coordinates never needs parameters in the match.
-/

namespace KnightModel.RankTwo.Scott

universe u v w

/-- The algebra of initial-interval charts acting on frames of one line. -/
structure FrameAction (C F : Type _) where
  one : C
  comp : C → C → C
  act : F → C → F
  proper : C → Prop
  act_one : ∀ f, act f one = f
  act_comp : ∀ f h k, act f (comp h k) = act (act f h) k
  compare : ∀ u v, (∃ h, act u h = v) ∨ ∃ h, proper h ∧ act v h = u
  higher : ∀ u, ∃ z k, proper k ∧ act z k = u
  paste : ∀ h k, proper h → proper k → ∃ K, comp K h = k

namespace FrameAction

variable {C F P : Type _}

/-- Solve a prescribed proper transition above a retained frame. -/
theorem solveAbove (A : FrameAction C F) (u : F) (h : C) (hh : A.proper h) :
    ∃ z, A.act z h = u := by
  obtain ⟨z₀, k, hk, hu⟩ := A.higher u
  obtain ⟨K, hK⟩ := A.paste h k hh hk
  exact ⟨A.act z₀ K, (A.act_comp _ _ _).symm.trans ((congrArg (A.act z₀) hK).trans hu)⟩

/-- Index points and vectors form the base sort P; they are independent of the anchor. -/
def read (A : FrameAction C F) (u : F) : P ⊕ C → P ⊕ F
  | .inl p => .inl p
  | .inr c => .inr (A.act u c)

def rebase (A : FrameAction C F) (h : C) : P ⊕ C → P ⊕ C
  | .inl p => .inl p
  | .inr c => .inr (A.comp h c)

theorem read_rebase (A : FrameAction C F) (u : F) (h : C) (c : P ⊕ C) :
    A.read u (A.rebase h c) = A.read (A.act u h) c := by
  cases c with
  | inl => rfl
  | inr c => exact congrArg Sum.inr (A.act_comp _ _ c)

end FrameAction

/-- Base matches pair parameters and programs. A move may enlarge the finite index
correspondence, retaining its old matches. This interface involves no actual frames. -/
structure CoordinateMatches {CL FL CR FR : Type _} (PL PR : Type _)
    (L : FrameAction CL FL) (R : FrameAction CR FR) where
  State : Type
  param : State → PL → PR → Prop
  code : State → CL → CR → Prop
  one : ∀ p, code p L.one R.one
  comp : ∀ {p h k h' k'}, code p h h' → code p k k' → code p (L.comp h k) (R.comp h' k')
  proper : ∀ {p h h'}, code p h h' → (L.proper h ↔ R.proper h')
  refines : State → State → Prop
  keepParam : ∀ {p q}, refines p q → ∀ {a b}, param p a b → param q a b
  keepCode : ∀ {p q}, refines p q → ∀ {a b}, code p a b → code q a b
  paramForth : ∀ p a, ∃ q b, refines p q ∧ param q a b
  paramBack : ∀ p b, ∃ q a, refines p q ∧ param q a b
  codeForth : ∀ p a, ∃ q b, refines p q ∧ code q a b
  codeBack : ∀ p b, ∃ q a, refines p q ∧ code q a b

namespace CoordinateMatches

variable {PL PR CL FL CR FR : Type _} {L : FrameAction CL FL} {R : FrameAction CR FR}
variable (G : CoordinateMatches PL PR L R)

def same (p : G.State) : PL ⊕ CL → PR ⊕ CR → Prop
  | .inl a, .inl b => G.param p a b
  | .inr a, .inr b => G.code p a b
  | _, _ => False

theorem keepSame {p q : G.State} (e : G.refines p q) {a b} (h : G.same p a b) :
    G.same q a b := by
  cases a <;> cases b
  case inl.inl => exact G.keepParam e h
  case inr.inr => exact G.keepCode e h
  all_goals exact False.elim h

theorem same_rebase {p : G.State} {a b} {h k} (hh : G.code p h k) (m : G.same p a b) :
    G.same p (L.rebase h a) (R.rebase k b) := by
  cases a <;> cases b
  case inl.inl => exact m
  case inr.inr => exact G.comp hh m
  all_goals exact False.elim m

/-- Witness the matching of selected elements using a single anchor on each side. -/
structure Position {n : Nat} (s : Tuple (PL ⊕ FL) n) (t : Tuple (PR ⊕ FR) n) where
  state : G.State
  left : FL
  right : FR
  a : Tuple (PL ⊕ CL) n
  b : Tuple (PR ⊕ CR) n
  agree : ∀ i, G.same state (a i) (b i)
  leftRead : ∀ i, L.read left (a i) = s i
  rightRead : ∀ i, R.read right (b i) = t i

namespace Position

variable {G} {n : Nat} {s : Tuple (PL ⊕ FL) n} {t : Tuple (PR ⊕ FR) n}

def enlarge (p : G.Position s t) {q : G.State} (e : G.refines p.state q) :
    G.Position s t :=
  { p with state := q, agree := fun i => G.keepSame e (p.agree i) }

/-- Composition retains the interpretations of all previously selected items. -/
def reanchor (p : G.Position s t) (u : FL) (v : FR) {h k}
    (hh : G.code p.state h k) (hl : L.act u h = p.left) (hr : R.act v k = p.right) :
    G.Position s t where
  state := p.state
  left := u
  right := v
  a := fun i => L.rebase h (p.a i)
  b := fun i => R.rebase k (p.b i)
  agree := fun i => G.same_rebase hh (p.agree i)
  leftRead i := by rw [L.read_rebase, hl, p.leftRead]
  rightRead i := by rw [R.read_rebase, hr, p.rightRead]

def add (p : G.Position s t) (a b) (hab : G.same p.state a b) :
    G.Position (push (L.read p.left a) s) (push (R.read p.right b) t) where
  state := p.state
  left := p.left
  right := p.right
  a := push a p.a
  b := push b p.b
  agree := Fin.cases hab p.agree
  leftRead := Fin.cases rfl p.leftRead
  rightRead := Fin.cases rfl p.rightRead

theorem forth (p : G.Position s t) (x : PL ⊕ FL) :
    ∃ y, Nonempty (G.Position (push x s) (push y t)) := by
  cases x with
  | inl x =>
    obtain ⟨q, y, e, m⟩ := G.paramForth p.state x
    exact ⟨.inl y, ⟨(p.enlarge e).add (.inl x) (.inl y) m⟩⟩
  | inr x =>
    rcases L.compare p.left x with ⟨h, hx⟩ | ⟨h, hp, hx⟩
    · obtain ⟨q, k, e, m⟩ := G.codeForth p.state h
      subst x
      exact ⟨.inr (R.act p.right k), ⟨(p.enlarge e).add (.inr h) (.inr k) m⟩⟩
    · obtain ⟨q, k, e, m⟩ := G.codeForth p.state h
      obtain ⟨y, hy⟩ := R.solveAbove p.right k ((G.proper m).mp hp)
      let p' := (p.enlarge e).reanchor x y m hx hy
      have out := p'.add (.inr L.one) (.inr R.one) (G.one _)
      change G.Position (push (.inr (L.act x L.one)) s)
        (push (.inr (R.act y R.one)) t) at out
      rw [L.act_one, R.act_one] at out
      exact ⟨.inr y, ⟨out⟩⟩

theorem back (p : G.Position s t) (y : PR ⊕ FR) :
    ∃ x, Nonempty (G.Position (push x s) (push y t)) := by
  cases y with
  | inl y =>
    obtain ⟨q, x, e, m⟩ := G.paramBack p.state y
    exact ⟨.inl x, ⟨(p.enlarge e).add (.inl x) (.inl y) m⟩⟩
  | inr y =>
    rcases R.compare p.right y with ⟨k, hy⟩ | ⟨k, hp, hy⟩
    · obtain ⟨q, h, e, m⟩ := G.codeBack p.state k
      subst y
      exact ⟨.inr (L.act p.left h), ⟨(p.enlarge e).add (.inr h) (.inr k) m⟩⟩
    · obtain ⟨q, h, e, m⟩ := G.codeBack p.state k
      obtain ⟨x, hx⟩ := L.solveAbove p.left h ((G.proper m).mpr hp)
      let p' := (p.enlarge e).reanchor x y m hx hy
      have out := p'.add (.inr L.one) (.inr R.one) (G.one _)
      change G.Position (push (.inr (L.act x L.one)) s)
        (push (.inr (R.act y R.one)) t) at out
      rw [L.act_one, R.act_one] at out
      exact ⟨.inr x, ⟨out⟩⟩

end Position

/-- Atomic tests are checked in a single pair of coordinate charts. The two extension
laws for actual frames are conclusions, obtained by moving the anchors. -/
def system {S : Nat → Type u} (D : Model S (PL ⊕ FL)) (E : Model S (PR ⊕ FR))
    (atomic : ∀ (p : G.State) (u : FL) (v : FR) {n : Nat}
      (a : Tuple (PL ⊕ CL) n) (b : Tuple (PR ⊕ CR) n), (∀ i, G.same p (a i) (b i)) →
      ∀ r : Atom S n, r.Holds D (L.read u ∘ a) ↔ r.Holds E (R.read v ∘ b)) :
    BackAndForth D E where
  matchTuples := fun s t => Nonempty (G.Position s t)
  atoms := by
    rintro n s t ⟨p⟩ r
    have hl : L.read p.left ∘ p.a = s := funext p.leftRead
    have hr : R.read p.right ∘ p.b = t := funext p.rightRead
    simpa only [hl, hr] using atomic p.state p.left p.right p.a p.b p.agree r
  forth := fun ⟨p⟩ => p.forth
  back := fun ⟨p⟩ => p.back

/-- The initial match uses arbitrary anchor frames. -/
def empty (p : G.State) (u : FL) (v : FR) :
    G.Position (n := 0) Fin.elim0 Fin.elim0 where
  state := p
  left := u
  right := v
  a := Fin.elim0
  b := Fin.elim0
  agree := fun i => i.elim0
  leftRead := fun i => i.elim0
  rightRead := fun i => i.elim0

end CoordinateMatches
end KnightModel.RankTwo.Scott
