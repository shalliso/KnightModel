/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.Words
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Conditions for the Knight Group Forcing

A `Condition` is an ω-sequence of `FixingPartialAut ℚ` — one partial fixing automorphism
per generator index — with only finitely many non-trivial entries.  Conditions are the
forcing poset: `p ≤ q` means `p` *extends* `q` (every graph pair of `q` also appears in `p`,
so `p` carries more information).

`evalLetter` and `evalWord` run a word against a condition to produce a partial output,
returning `none` if any required graph entry is missing.

## Main definitions

* `Condition`: the ω-sequence type with the extension order.
* `evalLetter p l a`: partial evaluation of a single letter at `a` under `p`.
* `evalWord p w a`: sequential composition of `evalLetter` over a word `w`.
* `Condition.Faithful p`: no two distinct letters send the same point to the same image.

## Main results

* `Condition.faithful_extension`: faithfulness is preserved by `CanExtend` extensions.

## Tags

knight group, condition, forcing, evalWord, faithful
-/

/-! ## The Condition Structure -/

/-- A `Condition` is an ω-sequence of fixing partial order-automorphisms of `ℚ`.
    The extension order `p ≤ q` means `p` has strictly more defined pairs than `q`. -/
@[ext]
structure Condition where
  seq : ℕ → FixingPartialAut ℚ

namespace Condition

instance : CoeFun Condition (fun _ => ℕ → FixingPartialAut ℚ) where
  coe := Condition.seq

/-- A `Condition.Extension` records a `Condition` that extends `p` at index `n` by the pair
    `(a, b)`: `seq n` is the extended fixing partial aut, all other indices unchanged. -/
structure Extension (p : Condition) (n : ℕ) (a b : ℚ) extends Condition where
  spec : ∃ (ext : (p n).Extension a b), seq n = ext ∧ ∀ i ≠ n, seq i = p i

instance {p : Condition} {n : ℕ} {a b : ℚ} : CoeOut (p.Extension n a b) Condition where
  coe := Extension.toCondition

/-- Predicate: `p` can be extended at index `n` by adding the pair `(a, b)`, i.e.
    the fixing partial aut `p n` satisfies `FixingPartialAut.CanExtend a b`. -/
structure CanExtend (p : Condition) (n : ℕ) (a b : ℚ) : Prop where
  canExtend : (p n).CanExtend a b

def CanExtend.toExtension {p : Condition} {n : ℕ} {a b : ℚ}
    (h : p.CanExtend n a b) : p.Extension n a b where
  seq := fun i => if i = n then h.canExtend.toExtension else p i
  spec := by
    use h.canExtend.toExtension
    constructor
    · simp
    · intro i hi
      simp [hi]

/-- The inverse condition: apply the inverse of each fixing partial automorphism. -/
instance : InvolutiveInv Condition where
  inv p := { seq n := (p n)⁻¹ }
  inv_inv p := by ext n; simp

@[simp] lemma inv_seq (p : Condition) (n : ℕ) : (p⁻¹).seq n = (p n)⁻¹ := rfl

def empty : Condition where
  seq := fun _ => ∅

instance : Inhabited Condition := ⟨empty⟩

instance : EmptyCollection Condition := ⟨empty⟩

/-- Forcing order: `p ≤ q` means `p` extends `q`, i.e. `p` has all the graph pairs of `q`
    and possibly more. This matches the `KnightCondition` preorder convention. -/
instance : Preorder Condition where
  le p q := ∀ n, (q n).graph ⊆ (p n).graph
  le_refl _ _ := le_refl _
  le_trans _ _ _ hpq hqr n := (hqr n).trans (hpq n)

/-- An extension `p'` of `p` satisfies `p' ≤ p`, i.e. has strictly more defined pairs. -/
lemma Extension.le {p : Condition} {n : ℕ} {a b : ℚ} (p' : p.Extension n a b) :
    (p' : Condition) ≤ p := by
  intro i
  obtain ⟨ext, hext, hother⟩ := p'.spec
  by_cases hi : i = n
  · subst hi; rw [hext, ext.spec]; exact Set.subset_union_left
  · rw [hother i hi]

end Condition


/-! ## Word Evaluation -/

section Eval

/-- Evaluate a single letter `(n, false)` (forward) or `(n, true)` (inverse) at point `a`
    under condition `p`.  Returns `none` if the required graph entry is missing. -/
noncomputable def evalLetter (p : Condition) : Letter → ℚ → Option ℚ
  | (n, false), a => (p n).apply? a
  | (n, true),  a => (p n).inv.apply? a

/-- Evaluate a word by sequentially applying `evalLetter` left-to-right, threading through
    `Option` via `bind`.  Returns `none` if any letter fails to evaluate. -/
noncomputable def evalWord (p : Condition) : Word → ℚ → Option ℚ
  | [],     a => some a
  | l :: w, a => (evalLetter p l a).bind (evalWord p w)

lemma evalLetter_letterInv (p : Condition) (l : Letter) (a b : ℚ)
    (h : evalLetter p l a = some b) : evalLetter p l⁻¹ b = some a := by
  obtain ⟨n, bl⟩ := l
  cases bl <;> simp only [evalLetter, letter_inv_def] at h ⊢
  · have hmem := PartialInj.mem_graph_of_apply? h
    exact PartialInj.apply?_of_mem hmem
  · have hmem := PartialInj.mem_graph_of_apply? h
    exact PartialInj.apply?_of_mem hmem

/-- Evaluating a letter under `p⁻¹` is the same as evaluating the inverse letter under `p`. -/
lemma evalLetter_inv_condition (p : Condition) (l : Letter) (a : ℚ) :
    evalLetter p⁻¹ l a = evalLetter p l⁻¹ a := by
  obtain ⟨n, b⟩ := l
  cases b <;>
    simp [evalLetter, Condition.inv_seq, letter_inv_def,
          FixingPartialAut.inv, PartialIso.symm, PartialInj.symm]

/-- If `p' ≤ p` (i.e. `p'` extends `p`) and `p` successfully evaluates a word,
    then `p'` evaluates it to the same result. -/
lemma evalWord_le {p p' : Condition} (w : Word) (c d : ℚ)
    (hle : p' ≤ p) (heval : evalWord p w c = some d) : evalWord p' w c = some d := by
  induction w generalizing c with
  | nil =>
    simp only [evalWord, Option.some.injEq] at heval ⊢
    exact heval
  | cons l w ih =>
    simp only [evalWord] at heval ⊢
    obtain ⟨n, b⟩ := l
    cases b <;> simp only [evalLetter] at heval ⊢
    · -- b = false: forward direction
      cases hp : (p n).apply? c with
      | none => simp [hp] at heval
      | some c' =>
        simp only [hp, Option.bind_some] at heval
        have hp' : (p' n).apply? c = some c' :=
          PartialInj.apply?_of_graph_subset (hle n) hp
        simp only [hp', Option.bind_some]
        exact ih c' heval
    · -- b = true: inverse direction
      cases hp : (p n).inv.apply? c with
      | none => simp [hp] at heval
      | some c' =>
        simp only [hp, Option.bind_some] at heval
        have hp' : (p' n).inv.apply? c = some c' := by
          have : (p n).inv.graph ⊆ (p' n).inv.graph :=
            PartialInj.symm_graph_subset (hle n)
          exact PartialInj.apply?_of_graph_subset this hp
        simp only [hp', Option.bind_some]
        exact ih c' heval

/-- If a letter evaluates in p, it evaluates to the same result in any extension p'. -/
lemma evalLetter_le {p p' : Condition} {l : Letter} {c d : ℚ}
    (hle : p' ≤ p) (heval : evalLetter p l c = some d) : evalLetter p' l c = some d := by
  obtain ⟨n, b⟩ := l
  cases b <;> simp only [evalLetter] at heval ⊢
  · exact PartialInj.apply?_of_graph_subset (hle n) heval
  · exact PartialInj.apply?_of_graph_subset (PartialInj.symm_graph_subset (hle n)) heval

/-- If a letter evaluates in p, it evaluates to the same result in any extension p'. -/
lemma evalLetter_eq_of_extension {p : Condition} {n : ℕ} {a b c d : ℚ} {l : Letter}
    (p' : p.Extension n a b)
    (heval : evalLetter p l c = some d) : evalLetter p'.toCondition l c = some d :=
  evalLetter_le p'.le heval

/-! ### Helpers for evaluation at an extension -/

/-- If the letter index `m` differs from `n`, then `evalLetter` agrees on `p` and `p'`. -/
lemma evalLetter_eq_of_ne_index {p : Condition} {n : ℕ} {a b : ℚ}
    (p' : p.Extension n a b) {m : ℕ} (hm : m ≠ n) (bl : Bool) (c : ℚ) :
    evalLetter p'.toCondition (m, bl) c = evalLetter p (m, bl) c := by
  obtain ⟨_, _, hother⟩ := p'.spec
  -- p'.toCondition m = p m since m ≠ n (the extension only modifies index n)
  have hseq : p'.toCondition m = p m := hother m hm
  cases bl <;> simp only [evalLetter, hseq]

/-- In an extension of `p` by `(a, b)` at `n`, the forward letter `(n, false)` evaluates
    `a` to `b`. -/
lemma evalLetter_extension_fwd {p : Condition} {n : ℕ} {a b : ℚ}
    (p' : p.Extension n a b) :
    evalLetter p'.toCondition (n, false) a = some b := by
  obtain ⟨ext, hext, _⟩ := p'.spec
  simp only [evalLetter]
  show (p'.seq n).apply? a = some b
  rw [hext]
  apply PartialInj.apply?_of_mem
  show (a, b) ∈ (↑ext : PartialIso ℚ ℚ).toPartialInj.graph
  rw [ext.spec]
  exact Set.mem_union_right _ rfl

/-- In an extension of `p` by `(a, b)` at `n`, the inverse letter `(n, true)` evaluates
    `b` to `a`. -/
lemma evalLetter_extension_inv {p : Condition} {n : ℕ} {a b : ℚ}
    (p' : p.Extension n a b) :
    evalLetter p'.toCondition (n, true) b = some a := by
  obtain ⟨ext, hext, _⟩ := p'.spec
  simp only [evalLetter]
  show (p'.seq n).inv.apply? b = some a
  rw [hext]
  apply PartialInj.apply?_of_mem
  -- (b, a) ∈ (↑ext).toPartialInj.inv.graph iff (a, b) ∈ (↑ext).graph (by definition of inv)
  change (a, b) ∈ (↑ext : PartialIso ℚ ℚ).toPartialInj.graph
  rw [ext.spec]
  exact Set.mem_union_right _ rfl

/-- If `(p n).apply? c = none` but the extension `p'` (which adds `(a, b)` at `n`)
    can evaluate `(n, false)` at `c`, then `c = a`. -/
lemma eq_a_of_extension_fwd_new {p : Condition} {n : ℕ} {a b c : ℚ}
    (p' : p.Extension n a b)
    (hp_none : (p n).apply? c = none)
    (hp'_some : (p'.toCondition n).apply? c ≠ none) : c = a := by
  obtain ⟨ext, hext, _⟩ := p'.spec
  have hext_eq : p'.toCondition n = (↑ext : FixingPartialAut ℚ) := hext
  -- Lift the non-none to a witness; hd : some d = (p'.toCondition n).apply? c
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hp'_some
  -- (c, d) ∈ (↑ext).graph = (p n).graph ∪ {(a, b)}
  have hmem : (c, d) ∈ (p n).graph ∪ {(a, b)} := by
    rw [← ext.spec]
    exact PartialInj.mem_graph_of_apply? (hext_eq ▸ hd.symm)
  cases hmem with
  | inl hp_mem =>
    -- (c, d) ∈ (p n).graph contradicts hp_none
    have := PartialInj.apply?_of_mem hp_mem
    rw [this] at hp_none; cases hp_none
  | inr hnew =>
    -- (c, d) = (a, b), so c = a
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hnew
    exact hnew.1

/-- If `(p n).inv.apply? c = none` but the extension `p'` (which adds `(a, b)` at `n`)
    can evaluate `(n, true)` at `c`, then `c = b`. -/
lemma eq_b_of_extension_inv_new {p : Condition} {n : ℕ} {a b c : ℚ}
    (p' : p.Extension n a b)
    (hp_none : (p n).inv.apply? c = none)
    (hp'_some : (p'.toCondition n).inv.apply? c ≠ none) : c = b := by
  obtain ⟨ext, hext, _⟩ := p'.spec
  have hext_eq : p'.toCondition n = (↑ext : FixingPartialAut ℚ) := hext
  -- Lift the non-none to a witness; hd : some d = (p'.toCondition n).inv.apply? c
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hp'_some
  -- (c, d) ∈ (↑ext).inv.graph, i.e. (d, c) ∈ (↑ext).graph = (p n).graph ∪ {(a, b)}
  have hmem_raw := PartialInj.mem_graph_of_apply? (hext_eq ▸ hd.symm)
  -- hmem_raw : (c, d) ∈ (↑ext).inv.graph (definitionally: (d, c) ∈ (↑ext).graph)
  have hmem' : (d, c) ∈ (p n).graph ∪ {(a, b)} := by
    rw [← ext.spec]; exact hmem_raw
  cases hmem' with
  | inl hp_mem =>
    -- (d, c) ∈ (p n).graph means (c, d) ∈ (p n).inv.graph, contradicting hp_none
    have hmem_p_inv : (c, d) ∈ (p n).toPartialInj.symm.graph := hp_mem
    have happ := PartialInj.apply?_of_mem hmem_p_inv
    -- hp_none : (p n)⁻¹.apply? c = none, definitionally (p n).toPartialInj.symm.apply? c = none
    have hp_none' : (p n).toPartialInj.symm.apply? c = none := hp_none
    exact (Option.some_ne_none d (happ.symm.trans hp_none')).elim
  | inr hnew =>
    -- (d, c) = (a, b), so c = b
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hnew
    exact hnew.2

end Eval

/-! ### Faithful condition -/

/-- A condition is faithful if no two distinct letters evaluate the same ordered pair. -/
def Condition.Faithful (p : Condition) : Prop :=
  ∀ (l l' : Letter) (a b : ℚ), a ≠ b →
    evalLetter p l a = some b → evalLetter p l' a = some b → l = l'


/-- If `evalLetter p' l x = some y` but `evalLetter p l x = none`, then `l` is
    the new forward or inverse letter: `l = (n, false)` with `x = a, y = b`,
    or `l = (n, true)` with `x = b, y = a`. -/
lemma new_edge_of_evalLetter_diff {p : Condition} {n : ℕ} {a b : ℚ}
    (p' : p.Extension n a b)
    {l : Letter} {x y : ℚ}
    (heval_p' : evalLetter p'.toCondition l x = some y)
    (heval_p : evalLetter p l x = none) :
    (l = (n, false) ∧ x = a ∧ y = b) ∨ (l = (n, true) ∧ x = b ∧ y = a) := by
  obtain ⟨m, d⟩ := l
  by_cases hm : m = n
  · subst hm
    cases d with
    | false =>
      left
      simp only [evalLetter] at heval_p heval_p'
      have hxa : x = a := eq_a_of_extension_fwd_new p' heval_p (by simp [heval_p'])
      refine ⟨rfl, hxa, ?_⟩
      have := evalLetter_extension_fwd p'
      simp only [evalLetter] at this
      rw [hxa] at heval_p'
      exact Option.some.inj (heval_p'.symm.trans this)
    | true =>
      right
      simp only [evalLetter] at heval_p heval_p'
      have hxb : x = b := eq_b_of_extension_inv_new p' heval_p (by simp [heval_p'])
      refine ⟨rfl, hxb, ?_⟩
      have := evalLetter_extension_inv p'
      simp only [evalLetter] at this
      rw [hxb] at heval_p'
      exact Option.some.inj (heval_p'.symm.trans this)
  · -- m ≠ n: extension doesn't change index m, evaluations are equal
    have heq := evalLetter_eq_of_ne_index p' hm d x
    rw [heq] at heval_p'
    exact absurd heval_p' (by simp only [evalLetter] at heval_p ⊢; cases d <;> simp [heval_p])

/-- Convert `¬evalLetter p l x = some y` to `evalLetter p l x = none` using the fact
    that extensions preserve existing evaluations. -/
lemma evalLetter_none_of_ext_ne {p : Condition} {n : ℕ} {a b : ℚ}
    (p' : p.Extension n a b) {l : Letter} {x y : ℚ}
    (heval_p' : evalLetter p'.toCondition l x = some y)
    (hne : ¬evalLetter p l x = some y) : evalLetter p l x = none := by
  rcases h : evalLetter p l x with _ | z
  · rfl
  · have heq : y = z := Option.some.inj (heval_p'.symm.trans (evalLetter_eq_of_extension p' h))
    exact absurd (heq ▸ h) hne

lemma Condition.faithful_extension {p : Condition} {n : ℕ} {a b : ℚ}
    (hp : p.Faithful)
    (hnew : a = b ∨ ∀ w : Word, evalWord p w a ≠ some b)
    (p' : p.Extension n a b) : p'.toCondition.Faithful := by
  intro l l' x y hxy heval_l heval_l'
  by_cases hl_old : evalLetter p l x = some y
  · by_cases hl'_old : evalLetter p l' x = some y
    · exact hp l l' x y hxy hl_old hl'_old
    · -- l' uses the new edge; show contradiction with hnew (or a = b ∧ x ≠ y)
      have hl'_none := evalLetter_none_of_ext_ne p' heval_l' hl'_old
      rcases new_edge_of_evalLetter_diff p' heval_l' hl'_none with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · -- x = a, y = b; l evaluates a → b in p
        rcases hnew with rfl | h_no
        · exact absurd rfl hxy
        · exact absurd (by simp [evalWord, hl_old]) (h_no [l])
      · -- x = b, y = a; l evaluates b → a in p; so l⁻¹ evaluates a → b
        rcases hnew with rfl | h_no
        · exact absurd rfl (Ne.symm hxy)
        · exact absurd (by simp [evalWord, evalLetter_letterInv p l x y hl_old]) (h_no [l⁻¹])
  · have hl_none := evalLetter_none_of_ext_ne p' heval_l hl_old
    rcases new_edge_of_evalLetter_diff p' heval_l hl_none with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- l = (n, false), x = a, y = b
      by_cases hl'_old : evalLetter p l' x = some y
      · rcases hnew with rfl | h_no
        · exact absurd rfl hxy
        · exact absurd (by simp [evalWord, hl'_old]) (h_no [l'])
      · have hl'_none := evalLetter_none_of_ext_ne p' heval_l' hl'_old
        rcases new_edge_of_evalLetter_diff p' heval_l' hl'_none with ⟨rfl, -, -⟩ | ⟨-, h1, -⟩
        · rfl
        · exact absurd h1 hxy
    · -- l = (n, true), x = b, y = a
      by_cases hl'_old : evalLetter p l' x = some y
      · rcases hnew with rfl | h_no
        · exact absurd rfl (Ne.symm hxy)
        · exact absurd (by simp [evalWord, evalLetter_letterInv p l' x y hl'_old]) (h_no [l'⁻¹])
      · have hl'_none := evalLetter_none_of_ext_ne p' heval_l' hl'_old
        rcases new_edge_of_evalLetter_diff p' heval_l' hl'_none with ⟨-, h1, -⟩ | ⟨rfl, -, -⟩
        · exact absurd h1 hxy
        · rfl
