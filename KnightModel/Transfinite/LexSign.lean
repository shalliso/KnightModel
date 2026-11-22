import KnightModel.RankTwo.ProgramDefinabilityFormula
import KnightModel.RankTwo.WordScalar
import KnightModel.RankTwo.SemilinearQE
import Mathlib.Tactic.Order

/-! # First sign of a semilinear comparison

The comparison scans a new scalar coordinate from the left. A finite cut list
ensures that a nonzero sign has a first cell, even over non-Archimedean spaces.
-/

namespace KnightModel.Transfinite.LexSign

open RankTwo RankTwo.Semilinear RankTwo.UnaryChoice

variable {V : Type*} [LinearOrder V]

def First (P Q : V → Prop) : Prop := ∃ t, P t ∧ ∀ s ≤ t, ¬ Q s

theorem First.asymm {P Q : V → Prop} : First P Q → ¬ First Q P := by
  rintro ⟨x,hx,ex⟩ ⟨y,hy,ey⟩
  rcases le_total x y with h | h
  · exact ey x h hx
  · exact ex y h hy

private def index (E : List V) (x : V) : Nat :=
  match E with
  | [] => 0
  | a :: es => (if x < a then 0 else if x = a then 1 else 2) + index es x

private theorem index_mono (E : List V) {x y : V} (h : x ≤ y) : index E x ≤ index E y := by
  induction E with
  | nil => exact le_rfl
  | cons a E ih =>
    simp only [index]
    apply Nat.add_le_add _ ih
    split_ifs <;> first | omega | order

private theorem sameCell_of_index (E : List V) {x y : V} (h : x ≤ y)
    (e : index E x = index E y) : SameCell E x y := by
  induction E with
  | nil => simp [SameCell]
  | cons a E ih =>
    have hm := index_mono E h
    simp only [index] at e
    have marks : (x < a ↔ y < a) ∧ (a < x ↔ a < y) := by
      split_ifs at e <;> first | omega | (constructor <;> constructor <;> intro <;> order)
    have rest : index E x = index E y := by
      split_ifs at e <;> first | omega | order
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact marks
    · exact ih rest _ hb

/-- Earliest nonzero sign for two disjoint predicates constant on finitely many cells. -/
theorem first_or_first {P Q : V → Prop} (E : List V)
    (hp : ∀ x y, SameCell E x y → (P x ↔ P y))
    (hq : ∀ x y, SameCell E x y → (Q x ↔ Q y)) (dis : ∀ x, P x → ¬ Q x)
    (hne : ∃ x, P x ∨ Q x) : First P Q ∨ First Q P := by
  classical
  let H (n : Nat) := ∃ x, index E x = n ∧ (P x ∨ Q x)
  have ex : ∃ n, H n := by obtain ⟨x,hx⟩ := hne; exact ⟨_,x,rfl,hx⟩
  obtain ⟨x,hx,hcol⟩ := Nat.find_spec ex
  have same (s : V) (hs : s ≤ x) (hs' : P s ∨ Q s) : SameCell E s x := by
    apply sameCell_of_index E hs
    exact le_antisymm (index_mono E hs) (hx ▸ Nat.find_min' ex ⟨s,rfl,hs'⟩)
  rcases hcol with p | q
  · exact .inl ⟨x,p,fun s hs q => dis x p ((hq _ _ (same s hs (.inr q))).mp q)⟩
  · exact .inr ⟨x,q,fun s hs p => dis x ((hp _ _ (same s hs (.inl p))).mp p) q⟩

/-- Compare two evaluations by successively inspecting scalar arguments. -/
def Ahead : Nat → (List V → Prop) → (List V → Prop) → List V → Prop
  | 0, P, _, w => P w
  | n+1, P, Q, w => First (fun t => Ahead n P Q (t :: w)) (fun t => Ahead n Q P (t :: w))

variable [AddCommGroup V] [Module ℚ V] [IsOrderedAddMonoid V]

abbrev WordTest (P : List V → Prop) : Prop := ∀ {k} (w : List (Term V k)),
  Definable {p | P (evalWord w p)}

/-- Repeated first-sign comparison stays first-order semilinear at every fixed arity. -/
theorem ahead_definable (qe : HeadElimination V) (n : Nat) {P Q : List V → Prop}
    (hp : WordTest P) (hq : WordTest Q) : WordTest (Ahead n P Q) := by
  induction n generalizing P Q with
  | zero => exact hp
  | succ n ih =>
    intro k w
    let tailVar (m : ℕ) : Fin m → Term V (m+1) := fun j => .var j.succ
    let outer := w.map (·.subst (tailVar k))
    let w' : List (Term V (k+1)) := .var 0 :: outer
    have ha := ih hp hq w'
    let nested := outer.map (·.subst (tailVar (k+1)))
    let w'' : List (Term V ((k+1)+1)) := .var 0 :: nested
    have hb := ih hq hp w''
    have hc := (def_term_le (V := V) (k := (k+1)+1) (.var 0) (.var (0 : Fin (k+1)).succ)).inter hb
    have hd := qe (ha.inter (qe hc).compl)
    convert hd using 1
    ext p
    change First _ _ ↔ ∃ t, Ahead n P Q (evalWord w' (Fin.cons t p)) ∧ ¬ ∃ s,
      Term.eval (.var 0) (Fin.cons s (Fin.cons t p)) ≤
        Term.eval (.var (0 : Fin (k+1)).succ) (Fin.cons s (Fin.cons t p)) ∧
      Ahead n Q P (evalWord w'' (Fin.cons s (Fin.cons t p)))
    simp only [First, w', w'', outer, nested, evalWord, List.map_cons, Term.eval,
      Fin.cons_zero, Fin.cons_succ, List.map_map, Function.comp_def,
      Term.eval_subst, tailVar, Fin.cons_succ, not_exists, not_and]

/-- Finitely many unary thresholds witness semilinearity after specializing the suffix. -/
theorem thresholds {P : List V → Prop} [PosSMulStrictMono ℚ V] (hp : WordTest P) (w : List V) :
    ∃ E : List V, ∀ x y, SameCell E x y → (P (x::w) ↔ P (y::w)) := by
  let word : List (Term V 1) := .var 0 :: w.map .const
  obtain ⟨φ,hφ⟩ := hp word
  let z : Fin 0 → V := Fin.elim0
  refine ⟨φ.cuts.map (·.eval z),fun x y hc => ?_⟩
  have hx := hφ (Fin.cons x z)
  have hy := hφ (Fin.cons y z)
  simp [word, evalWord, Function.comp_def, Term.eval] at hx hy
  exact hx.trans ((φ.holds_sameCell z x y hc).trans hy.symm)

end KnightModel.Transfinite.LexSign
