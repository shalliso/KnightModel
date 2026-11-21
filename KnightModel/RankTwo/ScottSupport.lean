import KnightModel.RankTwo.ScottLanguage

/-! # Finite support and coordinate matching

Coordinates with any finite number of support indices can be matched by successive
one-index moves. Program validity and properness need only be infinitarily definable
in the base. Neither an existential matching principle for new frames nor one for
new programs is assumed here.
-/

namespace KnightModel.RankTwo.Scott

universe u v

/-- A graph position for the base index sorts; order on positions is extension. -/
structure IndexConditions (I J : Type _) where
  State : Type
  graph : State → I → J → Prop
  left : ∀ p x, ∃ q y, (∀ a b, graph p a b → graph q a b) ∧ graph q x y
  right : ∀ p y, ∃ q x, (∀ a b, graph p a b → graph q a b) ∧ graph q x y

namespace IndexConditions
variable {I J : Type _} (G : IndexConditions I J)

def Extends (p q : G.State) : Prop := ∀ a b, G.graph p a b → G.graph q a b

def paired (p : G.State) {n} (s : Tuple I n) (t : Tuple J n) : Prop :=
  ∀ i, G.graph p (s i) (t i)

theorem leftTuple (p : G.State) {n} (s : Tuple I n) :
    ∃ q t, G.Extends p q ∧ G.paired q s t := by
  induction n generalizing p with
  | zero => exact ⟨p, Fin.elim0, fun _ _ h => h, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨q, t, e, m⟩ := ih p (fun i => s i.succ)
    obtain ⟨r, y, f, hy⟩ := G.left q (s 0)
    exact ⟨r, push y t, fun a b h => f _ _ (e a b h),
      Fin.cases hy (fun i => f _ _ (m i))⟩

theorem rightTuple (p : G.State) {n} (t : Tuple J n) :
    ∃ q s, G.Extends p q ∧ G.paired q s t := by
  induction n generalizing p with
  | zero => exact ⟨p, Fin.elim0, fun _ _ h => h, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨q, s, e, m⟩ := ih p (fun i => t i.succ)
    obtain ⟨r, x, f, hx⟩ := G.right q (t 0)
    exact ⟨r, push x s, fun a b h => f _ _ (e a b h),
      Fin.cases hx (fun i => f _ _ (m i))⟩

end IndexConditions

/-- A schema has a fixed finite number of free support indices. Invalid instance
parameters are represented by absence. Different schemas may represent the same value. -/
structure Coding (S : Nat → Type u) (I T : Type _) where
  eval : ∀ {n}, S n → Tuple I n → Option T
  covers : ∀ t : T, ∃ (n : Nat) (s : S n) (a : Tuple I n), eval s a = some t

variable {I J PL PR CL FL CR FR : Type _} {L : FrameAction CL FL} {R : FrameAction CR FR}
variable {S : Nat → Type u} {Q : Nat → Type v} {U V : Type _}
variable (G : IndexConditions I J)

def matchCode (X : Coding S I U) (Y : Coding S J V) (p : G.State) (x : U) (y : V) : Prop :=
  ∃ (n : Nat) (s : S n) (a : Tuple I n) (b : Tuple J n),
    G.paired p a b ∧ X.eval s a = some x ∧ Y.eval s b = some y

namespace Coding

variable {G}

theorem keep {X : Coding S I U} {Y : Coding S J V} {p q} (e : G.Extends p q)
    {x y} (m : matchCode G X Y p x y) : matchCode G X Y q x y := by
  obtain ⟨n, s, a, b, ab, hx, hy⟩ := m
  exact ⟨n, s, a, b, fun i => e _ _ (ab i), hx, hy⟩

/-- Domains of the same schema agree when its support indices match. -/
def DomainsMatch (G : IndexConditions I J) (X : Coding S I U) (Y : Coding S J V) : Prop :=
  ∀ {n} (s : S n) {p a b}, G.paired p a b →
    ((∃ x, X.eval s a = some x) ↔ ∃ y, Y.eval s b = some y)

theorem leftCode {X : Coding S I U} {Y : Coding S J V} (domains : DomainsMatch G X Y)
    (p : G.State) (x : U) : ∃ q y, G.Extends p q ∧ matchCode G X Y q x y := by
  obtain ⟨n, s, a, hx⟩ := X.covers x
  obtain ⟨q, b, e, m⟩ := G.leftTuple p a
  obtain ⟨y, hy⟩ := (domains s m).mp ⟨x, hx⟩
  exact ⟨q, y, e, n, s, a, b, m, hx, hy⟩

theorem rightCode {X : Coding S I U} {Y : Coding S J V} (domains : DomainsMatch G X Y)
    (p : G.State) (y : V) : ∃ q x, G.Extends p q ∧ matchCode G X Y q x y := by
  obtain ⟨n, s, b, hy⟩ := Y.covers y
  obtain ⟨q, a, e, m⟩ := G.rightTuple p b
  obtain ⟨x, hx⟩ := (domains s m).mpr ⟨y, hy⟩
  exact ⟨q, x, e, n, s, a, b, m, hx, hy⟩

/-- Uniform infinitary definability in the actual index language suffices for domain transfer. -/
theorem domainsMatch_of_formula {T : Nat → Type _} {D : Model T I} {E : Model T J}
    (BF : BackAndForth D E) (base : ∀ {p n} {a : Tuple I n} {b}, G.paired p a b →
      BF.matchTuples a b) (X : Coding S I U) (Y : Coding S J V)
    (d : ∀ {n}, S n → Formula T n)
    (left : ∀ {n} (s : S n) a, (d s).Holds D a ↔ ∃ x, X.eval s a = some x)
    (right : ∀ {n} (s : S n) b, (d s).Holds E b ↔ ∃ y, Y.eval s b = some y) :
    DomainsMatch G X Y :=
  fun s _ _ _ m => (left s _).symm.trans ((BF.holds_iff _ (base m)).trans (right s _))

end Coding

def appendTuple {T : Type _} {n k} (a : Tuple T n) (b : Tuple T k) : Tuple T (n+k) :=
  Fin.addCases a b

theorem IndexConditions.paired_append {G : IndexConditions I J} {p : G.State} {n k}
    {a : Tuple I n} {b : Tuple J n} {c : Tuple I k} {d : Tuple J k}
    (h : G.paired p a b) (j : G.paired p c d) :
    G.paired p (appendTuple a c) (appendTuple b d) := by
  intro i
  refine Fin.addCases (fun ii => ?_) (fun ii => ?_) i <;>
    simp only [appendTuple, Fin.addCases_left, Fin.addCases_right]
  · exact h ii
  · exact j ii

/-- A scheme-language compiler for the identity and composition of total coordinates. -/
structure CodeOps (Q : Nat → Type v) where
  ident : Q 0
  comp : ∀ {n k}, Q n → Q k → Q (n+k)

structure CodeOps.Correct (ops : CodeOps Q) (X : Coding Q I CL) (A : FrameAction CL FL) : Prop where
  ident : X.eval ops.ident Fin.elim0 = some A.one
  comp : ∀ {n k} (h : Q n) (l : Q k) {a b c d}, X.eval h a = some c → X.eval l b = some d →
    X.eval (ops.comp h l) (appendTuple a b) = some (A.comp c d)

/-- Construct all code moves from finite support and index moves. -/
def coordinates (PX : Coding S I PL) (PY : Coding S J PR)
    (CX : Coding Q I CL) (CY : Coding Q J CR)
    (pd : Coding.DomainsMatch G PX PY) (cd : Coding.DomainsMatch G CX CY)
    (ops : CodeOps Q) (ox : ops.Correct CX L) (oy : ops.Correct CY R)
    (proper : ∀ {n} (s : Q n) {p a b c d}, G.paired p a b →
      CX.eval s a = some c → CY.eval s b = some d → (L.proper c ↔ R.proper d)) :
    CoordinateMatches PL PR L R where
  State := G.State
  param := matchCode G PX PY
  code := matchCode G CX CY
  one p := ⟨0, ops.ident, Fin.elim0, Fin.elim0, fun i => i.elim0, ox.ident, oy.ident⟩
  comp := by
    rintro p c d c' d' ⟨n,h,a,b,m,l,r⟩ ⟨k,g,x,y,e,j,z⟩
    exact ⟨n+k, ops.comp h g, appendTuple a x, appendTuple b y, IndexConditions.paired_append m e,
      ox.comp h g l j, oy.comp h g r z⟩
  proper := by
    rintro p c d ⟨n,s,a,b,m,l,r⟩
    exact proper s m l r
  refines := G.Extends
  keepParam := fun h _ _ m => Coding.keep h m
  keepCode := fun h _ _ m => Coding.keep h m
  paramForth := Coding.leftCode pd
  paramBack := Coding.rightCode pd
  codeForth := Coding.leftCode cd
  codeBack := Coding.rightCode cd

end KnightModel.RankTwo.Scott
