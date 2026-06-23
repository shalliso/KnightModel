/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.Condition
import KnightModel.KnightAutGroup.EvalGraph

/-!
# Knight Conditions

A `KnightCondition` is a `Condition` satisfying four invariants that make it safe to
extend without introducing cycles or ambiguities:

* `finite_support`: only finitely many generator indices `n` have non-trivial partial auts.
* `finite`: each `p.seq n` has a finite graph.
* `acyclic`: the evaluation graph `p.EvalGraph` is acyclic.
* `faithful`: no two distinct letters evaluate the same ordered pair.

The forcing order `p ≤ q` (p extends q) lifts to this type.

## Main definitions

* `KnightCondition`: the main structure with the four invariants.
* `KnightCondition.CanExtend p n a b`: conditions under which `p` can be extended at index `n`
  by adding the pair `(a, b)`.  The key extra condition is `noNewCycles`.
* `KnightCondition.inv`: pointwise inverse condition.

## Main results

* `KnightCondition.evalWord_fixing`: if `evalWord p w b = some b` and `a ≤ b`, then
  `evalWord p w a = some a`.  Proved by strong induction on the walk length in `p.EvalGraph`.

## Tags

knight condition, acyclic, faithful, fixing, forcing
-/

/-! ## The KnightCondition Structure -/

/-- A `KnightCondition` is a `Condition` with finitely many non-trivial partial automorphisms,
    each with a finite graph, and whose evaluation graph is acyclic and faithful. -/
@[ext]
structure KnightCondition extends Condition where
  finite_support : {n | seq n ≠ ∅}.Finite
  finite : ∀ n : ℕ, (seq n).graph.Finite
  acyclic  : toCondition.EvalGraph.IsAcyclic
  faithful : toCondition.Faithful

instance : Coe KnightCondition Condition where
  coe := KnightCondition.toCondition

namespace KnightCondition

def empty : KnightCondition where
  seq := fun _ => ∅
  finite_support := by
    convert Set.finite_empty
    ext n; simp
  finite := fun _ => Set.finite_empty
  acyclic := by
    intro v c hcycle
    have h3 := hcycle.three_le_length
    cases c with
    | nil => simp at h3
    | cons hadj rest =>
      obtain ⟨-, ⟨n, bl⟩, hl⟩ := (Condition.evalGraph_adj_iff _ _ _).mp hadj
      cases bl <;> simp only [evalLetter] at hl
      · exact absurd (hl.symm.trans (PartialInj.apply?_eq_none (fun ⟨_, hx⟩ => hx)))
          (Option.some_ne_none _)
      · exact absurd (hl.symm.trans (PartialInj.apply?_eq_none (fun ⟨_, hx⟩ => hx)))
          (Option.some_ne_none _)
  faithful := by
    intro l l' a b hab hl hl'
    obtain ⟨n, bl⟩ := l
    cases bl <;> simp only [evalLetter] at hl
    · exact absurd (hl.symm.trans (PartialInj.apply?_eq_none (fun ⟨_, hx⟩ => hx)))
        (Option.some_ne_none _)
    · exact absurd (hl.symm.trans (PartialInj.apply?_eq_none (fun ⟨_, hx⟩ => hx)))
        (Option.some_ne_none _)

instance : Inhabited KnightCondition := ⟨empty⟩

instance : EmptyCollection KnightCondition := ⟨empty⟩

instance : Preorder KnightCondition where
  le p q := ∀ n, (q.seq n).graph ⊆ (p.seq n).graph
  le_refl _ _ := le_refl _
  le_trans p q r hpq hqr n := le_trans (hqr n) (hpq n)

structure Extension (p : KnightCondition) (n : ℕ) (a b : ℚ) extends KnightCondition where
  spec : ∀ m, ∀ point ∈ (seq m).graph,
    point ∈ (p.seq m).graph ∨ (m = n ∧ point = ⟨a, b⟩)

/-- Conditions under which a `KnightCondition` can be extended by adding the pair `(a, b)`
    at generator index `n`.  Beyond the order-compatibility from `FixingPartialAut.CanExtend`,
    `noNewCycles` requires that `b` is not already reachable from `a` (or `a = b`),
    preventing the extension from introducing a cycle in the evaluation graph. -/
structure CanExtend (p : KnightCondition) (n : ℕ) (a b : ℚ) : Prop
    extends toCanExtendFPA : (p.seq n).CanExtend a b where
  noNewCycles : a = b ∨ ∀ w : Word, evalWord p w a ≠ some b

def CanExtend.toExtension {p : KnightCondition} {n : ℕ} {a b : ℚ}
    (h : p.CanExtend n a b) : p.Extension n a b where
  seq := fun m => if m = n then h.toCanExtendFPA.toExtension else p.seq m
  finite_support := by
    apply (p.finite_support.union (Set.finite_singleton n)).subset
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_cases hm' : m = n
    · exact Or.inr hm'
    · exact Or.inl (by simp only [if_neg hm'] at hm; exact hm)
  finite := by
    intro m
    by_cases hm : m = n
    · subst hm
      have : (if m = m
        then (h.toCanExtendFPA.toExtension : FixingPartialAut ℚ)
        else p.seq m).graph =
             h.toCanExtendFPA.toExtension.graph := by simp
      rw [this, h.toCanExtendFPA.toExtension.spec]
      exact (p.finite m).union (Set.finite_singleton _)
    · simp only [if_neg hm]; exact p.finite m
  acyclic := isAcyclic_of_canExtend
      (⟨h.toCanExtendFPA⟩ : Condition.CanExtend (p : Condition) n a b)
      h.noNewCycles p.faithful p.acyclic
  faithful := faithful_of_canExtend
      (⟨h.toCanExtendFPA⟩ : Condition.CanExtend (p : Condition) n a b)
      h.noNewCycles p.faithful p.acyclic
  spec := by
    intro m point hpoint
    by_cases hm : m = n
    · subst hm
      simp only [ite_true] at hpoint
      rw [h.toCanExtendFPA.toExtension.spec] at hpoint
      cases hpoint with
      | inl hp => exact Or.inl hp
      | inr hnew =>
        simp only [Set.mem_singleton_iff] at hnew
        exact Or.inr ⟨rfl, hnew⟩
    · simp only [if_neg hm] at hpoint
      exact Or.inl hpoint

lemma CanExtend.exists_extension {p : KnightCondition} {n : ℕ} {a b : ℚ}
    (h : p.CanExtend n a b)
    : ∃ q : KnightCondition, q ≤ p ∧ ⟨a, b⟩ ∈ (q.seq n).graph := by
  refine ⟨h.toExtension.toKnightCondition, ?le, ?mem⟩
  case le =>
    intro m
    by_cases hm : m = n
    · subst hm
      simp only [toExtension, ite_true]
      rw [h.toCanExtendFPA.toExtension.spec]
      exact Set.subset_union_left
    · simp only [toExtension, if_neg hm]
      exact le_refl _
  case mem =>
    simp only [toExtension, ite_true]
    rw [h.toCanExtendFPA.toExtension.spec]
    exact Set.mem_union_right _ (Set.mem_singleton _)

/-! ## Inverse of a KnightCondition -/

/-- The inverse of a `KnightCondition`: swap domain and range at every index. -/
noncomputable def inv (p : KnightCondition) : KnightCondition where
  seq n := (p.seq n).inv
  finite_support := by
    apply p.finite_support.subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    intro heq
    apply hn
    have hgraph_inv : ((p.seq n).inv : FixingPartialAut ℚ).graph = ∅ := by
      rw [heq]; rfl
    exact FixingPartialAut.ext hgraph_inv
  finite n := by
    have hfin : ((p.seq n).inv : FixingPartialAut ℚ).graph =
        (fun (x : ℚ × ℚ) => (x.2, x.1)) '' (p.seq n).graph := by
      ext ⟨a, b⟩
      simp [FixingPartialAut.inv, PartialIso.symm, PartialInj.symm, Set.mem_image]
    rw [hfin]
    exact (p.finite n).image _
  acyclic := evalGraph_inv_condition_eq p.toCondition ▸ p.acyclic
  faithful := by
    intro l l' a b hab hl hl'
    change evalLetter p.toCondition⁻¹ l a = some b at hl
    change evalLetter p.toCondition⁻¹ l' a = some b at hl'
    rw [evalLetter_inv_condition] at hl hl'
    have h := p.faithful l⁻¹ l'⁻¹ a b hab hl hl'
    calc l = l⁻¹⁻¹ := (inv_inv l).symm
         _ = l'⁻¹⁻¹ := congrArg (·⁻¹) h
         _ = l' := inv_inv l'

noncomputable instance : InvolutiveInv KnightCondition where
  inv := inv
  inv_inv p := by
    ext n ⟨a, b⟩
    simp [inv, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm]

@[simp]
lemma inv_seq (p : KnightCondition) (n : ℕ) : (p⁻¹).seq n = (p.seq n).inv := rfl

/-- The ordering on `KnightCondition` is reversed by inversion. -/
lemma inv_le_inv_iff {p q : KnightCondition} : p⁻¹ ≤ q⁻¹ ↔ p ≤ q := by
  constructor
  · intro h n ⟨a, b⟩ hab
    have hmem : (b, a) ∈ (p⁻¹.seq n).graph := h n (by
      simp only [inv_seq, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm,
                 Set.mem_setOf_eq]
      exact hab)
    simp only [inv_seq, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm,
               Set.mem_setOf_eq] at hmem
    exact hmem
  · intro h n ⟨a, b⟩ hab
    simp only [inv_seq, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm,
               Set.mem_setOf_eq]
    exact h n hab

/-! ### Auxiliary lemmas for evalWord_fixing -/

/-- If the walk induced by `w` from `a` back to `a` is nil, every letter in `w` fixes `a`. -/
private lemma allLettersFix_of_nil_walk {p : Condition} {w : Word} {a : ℚ}
    (h : evalWord p w a = some a)
    (hnil : Condition.walkOfEval p w a a h = .nil) :
    ∀ l ∈ w, evalLetter p l a = some a := by
  induction w with
  | nil => intro l hl; simp at hl
  | cons l w ih =>
    intro l' hl'
    have hcons := h
    simp only [evalWord] at hcons
    cases hla : evalLetter p l a with
    | none => simp [hla] at hcons
    | some c =>
      simp only [hla, Option.bind_some] at hcons
      by_cases hac : a = c
      · subst hac
        have htail : Condition.walkOfEval p w a a hcons = .nil := by
          have := Condition.walkOfEval_cons_eq h hla
          rw [Condition.walkOfEvalStep_fix] at this
          rw [← this]; convert hnil using 2
        rcases List.mem_cons.mp hl' with rfl | hl'w
        · exact hla
        · exact ih hcons htail l' hl'w
      · have hlen := Condition.walkOfEval_cons_length_pos h hla hac
        rw [hnil, SimpleGraph.Walk.length_nil] at hlen
        exact absurd hlen (by omega)

/-- `evalWord` preserves the order: if `a ≤ b` and both succeed, results satisfy `c ≤ d`. -/
private lemma evalWord_order_pres {p : KnightCondition} (w : Word) {a b c d : ℚ}
    (hab : a ≤ b)
    (ha : evalWord p w a = some c) (hb : evalWord p w b = some d) : c ≤ d := by
  induction w generalizing a b c d with
  | nil =>
    simp only [evalWord, Option.some.injEq] at ha hb
    exact ha ▸ hb ▸ hab
  | cons l w ih =>
    simp only [evalWord] at ha hb
    obtain ⟨n, bl⟩ := l
    cases bl <;> simp only [evalLetter] at ha hb
    · cases hla : (p.seq n).apply? a with
      | none => simp [hla] at ha
      | some a' =>
        simp only [hla, Option.bind_some] at ha
        cases hlb : (p.seq n).apply? b with
        | none => simp [hlb] at hb
        | some b' =>
          simp only [hlb, Option.bind_some] at hb
          exact ih ((p.seq n).toPartialIso.order_pres_iff
            (PartialInj.mem_graph_of_apply? hla)
            (PartialInj.mem_graph_of_apply? hlb) |>.mp hab) ha hb
    · cases hla : (p.seq n).inv.apply? a with
      | none => simp [hla] at ha
      | some a' =>
        simp only [hla, Option.bind_some] at ha
        cases hlb : (p.seq n).inv.apply? b with
        | none => simp [hlb] at hb
        | some b' =>
          simp only [hlb, Option.bind_some] at hb
          exact ih ((p.seq n).toPartialIso.symm.order_pres_iff
            (PartialInj.mem_graph_of_apply? hla)
            (PartialInj.mem_graph_of_apply? hlb) |>.mp hab) ha hb

/-- A letter that fixes `b` also fixes any `a ≤ b`. -/
private lemma evalLetter_fixes_of_le {p : KnightCondition} {l : Letter} {a b a' : ℚ}
    (hab : a ≤ b) (hfb : evalLetter p l b = some b) (hla : evalLetter p l a = some a') :
    a = a' := by
  obtain ⟨n, bl⟩ := l
  cases bl <;> simp only [evalLetter] at hfb hla
  · exact (p.seq n).fixing ⟨b, b⟩ (PartialInj.mem_graph_of_apply? hfb)
        ⟨a, a'⟩ (PartialInj.mem_graph_of_apply? hla) rfl hab
  · -- Convert inverse evaluations to forward ones, then apply fixing.
    have hfb_fwd : (p.seq n).apply? b = some b := by
      have := evalLetter_letterInv p.toCondition (n, true) b b (by simpa [evalLetter])
      simpa [evalLetter, letter_inv_def] using this
    have hla_fwd : (p.seq n).apply? a' = some a := by
      have := evalLetter_letterInv p.toCondition (n, true) a a' (by simpa [evalLetter])
      simpa [evalLetter, letter_inv_def] using this
    have ha'b : a' ≤ b := (p.seq n).toPartialIso.order_pres_iff
        (PartialInj.mem_graph_of_apply? hla_fwd)
        (PartialInj.mem_graph_of_apply? hfb_fwd) |>.mpr hab
    exact ((p.seq n).fixing ⟨b, b⟩ (PartialInj.mem_graph_of_apply? hfb_fwd)
        ⟨a', a⟩ (PartialInj.mem_graph_of_apply? hla_fwd) rfl ha'b).symm

/-- If all letters in `w` fix `b` and `a ≤ b`, then `evalWord p w a = some a`. -/
private lemma evalWord_fixes_of_all_fix_b {p : KnightCondition} {w : Word} {a b c : ℚ}
    (hab : a ≤ b) (hall_b : ∀ l ∈ w, evalLetter p l b = some b)
    (ha : evalWord p w a = some c) : c = a := by
  induction w generalizing a c with
  | nil =>
    simp only [evalWord, Option.some.injEq] at ha
    exact ha.symm
  | cons l w ih =>
    simp only [evalWord] at ha
    cases hla : evalLetter p l a with
    | none => simp [hla] at ha
    | some a' =>
      simp only [hla, Option.bind_some] at ha
      have heq : a = a' := evalLetter_fixes_of_le hab (hall_b l List.mem_cons_self) hla
      subst heq
      exact ih hab (fun l' hl' => hall_b l' (List.mem_cons.mpr (Or.inr hl'))) ha

/-- Structural decomposition: if `l` moves `b1 → b1'`, the full walk `l :: w2` from `b1`
    is not reduced, but the tail walk `w2` from `b1'` is reduced, then `w2` decomposes as
    `w_fix ++ [l⁻¹] ++ w_rest` where every letter in `w_fix` fixes `b1'`. -/
private lemma split_word_at_inverse {p : KnightCondition} {l : Letter} (w2 : Word)
    {b1 b1' b2 : ℚ}
    (hla_b : evalLetter (↑p) l b1 = some b1')
    (hb1_ne : b1 ≠ b1')
    (hb : evalWord (↑p) w2 b1' = some b2)
    (hWtail_red : (Condition.walkOfEval p.toCondition w2 b1' b2 hb).IsReduced)
    (hWfull_nred : ¬(Condition.walkOfEval p.toCondition (l :: w2) b1 b2
        (by simp [evalWord, hla_b, hb])).IsReduced) :
    ∃ w_fix w_rest,
      w2 = w_fix ++ [l⁻¹] ++ w_rest ∧
      ∀ l' ∈ w_fix, evalLetter (↑p) l' b1' = some b1' := by
  induction w2 generalizing b2 with
  | nil =>
    -- A single-edge walk is always reduced, contradicting hWfull_nred.
    exfalso
    simp only [evalWord, Option.some.injEq] at hb
    subst hb
    apply hWfull_nred
    rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_move hla_b hb1_ne]
    exact .cons_nil _
  | cons l2 w_rest ih =>
    -- Decompose evaluation of the tail (l2 :: w_rest) at b1'.
    have hb_orig := hb
    simp only [evalWord] at hb
    cases hl2_b : evalLetter (↑p) l2 b1' with
    | none => simp [hl2_b] at hb
    | some b1'' =>
    rw [hl2_b] at hb
    by_cases hb1'_eq : b1' = b1''
    · -- l2 fixes b1': recurse on w_rest.
      subst hb1'_eq
      have hW_tail_eq : Condition.walkOfEval p.toCondition (l2 :: w_rest) b1' b2 hb_orig =
          Condition.walkOfEval p.toCondition w_rest b1' b2 hb := by
        rw [Condition.walkOfEval_cons_eq _ hl2_b, Condition.walkOfEvalStep_fix]
      have hWred_rest : (Condition.walkOfEval p.toCondition w_rest b1' b2 hb).IsReduced :=
        hW_tail_eq ▸ hWtail_red
      have hWfull_nred_rest : ¬(Condition.walkOfEval p.toCondition (l :: w_rest) b1 b2
          (by simp [evalWord, hla_b, hb])).IsReduced := by
        intro hred
        apply hWfull_nred
        rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_move hla_b hb1_ne]
        rw [Condition.walkOfEval_cons_eq _ hla_b,
            Condition.walkOfEvalStep_move hla_b hb1_ne] at hred
        rw [hW_tail_eq]
        exact hred
      obtain ⟨w_fix', w_rest', hsplit, hfix'⟩ :=
        ih hb hWred_rest hWfull_nred_rest
      refine ⟨l2 :: w_fix', w_rest', by rw [hsplit]; rfl, ?_⟩
      intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'_mem
      · exact hl2_b
      · exact hfix' l' hl'_mem
    · -- l2 moves b1' → b1''. Use isReduced_cons_cons_iff to deduce b1'' = b1.
      have hWtail_exp :
          (SimpleGraph.Walk.cons
            (p.toCondition.evalGraph_adj_iff b1' b1'' |>.mpr ⟨hb1'_eq, l2, hl2_b⟩)
            (Condition.walkOfEval p.toCondition w_rest b1'' b2 hb)).IsReduced := by
        have hconv :
            (Condition.walkOfEval p.toCondition (l2 :: w_rest) b1' b2 hb_orig).IsReduced :=
          hWtail_red
        rwa [Condition.walkOfEval_cons_eq hb_orig hl2_b,
             Condition.walkOfEvalStep_move hl2_b hb1'_eq] at hconv
      have hb1''_eq : b1 = b1'' := by
        by_contra hne
        apply hWfull_nred
        rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_move hla_b hb1_ne,
            Condition.walkOfEval_cons_eq hb_orig hl2_b,
            Condition.walkOfEvalStep_move hl2_b hb1'_eq,
            SimpleGraph.Walk.isReduced_cons_cons_iff]
        exact ⟨hne, hWtail_exp⟩
      subst hb1''_eq
      -- l2 : b1' → b1 and l⁻¹ : b1' → b1, so by faithfulness l2 = l⁻¹.
      have hl2_eq : l2 = l⁻¹ := p.faithful l2 l⁻¹ b1' b1 hb1'_eq hl2_b
          (evalLetter_letterInv p.toCondition l b1 b1' hla_b)
      subst hl2_eq
      exact ⟨[], w_rest, rfl, fun _ h => (List.not_mem_nil h).elim⟩

/-- Pure evaluation cancellation: if `w_fix` is a list of letters fixing `b1'` (where `l`
    moves `b1 → b1'`) and `a ≤ b1`, then evaluating `l :: w_fix ++ [l⁻¹] ++ w_rest` at `a`
    equals evaluating `w_rest` at `a`. -/
private lemma cancel_inverse_pair_eval {p : KnightCondition} {l : Letter}
    {w_fix w_rest : Word} {a b1 b1' c : ℚ}
    (hab : a ≤ b1)
    (hla_b : evalLetter (↑p) l b1 = some b1')
    (_hb1_ne : b1 ≠ b1')
    (hfix : ∀ l' ∈ w_fix, evalLetter (↑p) l' b1' = some b1')
    (h : evalWord (↑p) (l :: w_fix ++ [l⁻¹] ++ w_rest) a = some c) :
    evalWord (↑p) w_rest a = some c := by
  -- Extract a' := evalLetter p l a from h.
  simp only [List.cons_append, evalWord] at h
  cases hla_a : evalLetter (↑p) l a with
  | none => simp [hla_a] at h
  | some a' =>
  rw [hla_a] at h
  simp only [Option.bind_some] at h
  -- a' ≤ b1' by order preservation on [l]
  have ha'_le : a' ≤ b1' := evalWord_order_pres (p := p) [l] hab
    (by simp [evalWord, hla_a]) (by simp [evalWord, hla_b])
  -- Helper: by induction on w_fix, evalWord p (w_fix ++ [l⁻¹] ++ w_rest) a' = some c
  -- implies evalWord p w_rest a = some c.
  suffices haux : ∀ (w_fix : Word) (a' : ℚ), a' ≤ b1' →
      (∀ l' ∈ w_fix, evalLetter (↑p) l' b1' = some b1') →
      evalLetter (↑p) l⁻¹ a' = some a →
      evalWord (↑p) (w_fix ++ [l⁻¹] ++ w_rest) a' = some c →
      evalWord (↑p) w_rest a = some c by
    exact haux w_fix a' ha'_le hfix (evalLetter_letterInv p.toCondition l a a' hla_a) h
  clear h hla_a ha'_le hfix
  intro w_fix a' ha'_le hfix hl_inv h
  induction w_fix generalizing a' with
  | nil =>
    -- h : evalWord p ([l⁻¹] ++ w_rest) a' = some c
    rw [List.nil_append] at h
    show evalWord (↑p) w_rest a = some c
    have h' : evalWord (↑p) (l⁻¹ :: w_rest) a' = some c := h
    simpa [evalWord, hl_inv] using h'
  | cons l1 w_fix' ih_fix =>
    simp only [List.cons_append, evalWord] at h
    cases hl1_a' : evalLetter (↑p) l1 a' with
    | none => simp [hl1_a'] at h
    | some a'' =>
    rw [hl1_a'] at h
    simp only [Option.bind_some] at h
    -- l1 fixes b1' and a' ≤ b1', so l1 fixes a' (a'' = a')
    have hfix_b : evalLetter (↑p) l1 b1' = some b1' :=
      hfix l1 List.mem_cons_self
    have ha''_eq : a' = a'' := evalLetter_fixes_of_le ha'_le hfix_b hl1_a'
    subst ha''_eq
    exact ih_fix a' ha'_le
      (fun l' hl' => hfix l' (List.mem_cons.mpr (Or.inr hl'))) hl_inv h

/-- If the walk of `w` from `b1` is not reduced, there is a shorter word with the same
    evaluations at `a` and `b1`, and a walk at least 2 shorter. -/
private lemma shorten_non_reduced_walk (p : KnightCondition) :
    ∀ (w : Word) (a b1 b2 c : ℚ) (_ : a ≤ b1)
    (hb : evalWord (↑p) w b1 = some b2)
    (_ : evalWord (↑p) w a = some c)
    (_ : ¬(Condition.walkOfEval p.toCondition w b1 b2 hb).IsReduced),
    ∃ w' : Word,
      ∃ (hb' : evalWord (↑p) w' b1 = some b2),
        evalWord (↑p) w' a = some c ∧
        (Condition.walkOfEval p.toCondition w' b1 b2 hb').length + 2 ≤
        (Condition.walkOfEval p.toCondition w b1 b2 hb).length := by
  intro w
  induction w with
  | nil =>
    intro a b1 b2 c _ hb _ hWred
    simp only [evalWord, Option.some.injEq] at hb; subst hb
    exact absurd .nil hWred
  | cons l w_tail ih_w =>
    intro a b1 b2 c hab hb ha hWred
    have hb_orig := hb
    have ha_orig := ha
    simp only [evalWord] at hb ha
    cases hla_b : evalLetter (↑p) l b1 with
    | none => simp [hla_b] at hb
    | some b1' =>
    cases hla_a : evalLetter (↑p) l a with
    | none => simp [hla_a] at ha
    | some a' =>
    rw [hla_b] at hb; rw [hla_a] at ha
    have ha'_le : a' ≤ b1' := evalWord_order_pres (p := p) [l] hab
      (by simp [evalWord, hla_a]) (by simp [evalWord, hla_b])
    by_cases hb1_eq : b1 = b1'
    · -- l fixes b1: peel it off and recurse on w_tail
      subst hb1_eq
      have ha_eq : a = a' := evalLetter_fixes_of_le hab hla_b hla_a
      subst ha_eq
      have hW_eq : Condition.walkOfEval p.toCondition (l :: w_tail) b1 b2 hb_orig =
          Condition.walkOfEval p.toCondition w_tail b1 b2 hb := by
        rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_fix]
      obtain ⟨w', hb', ha', hlen'⟩ := ih_w a b1 b2 c hab hb ha (hW_eq ▸ hWred)
      exact ⟨w', hb', ha', hW_eq ▸ hlen'⟩
    · by_cases hWred_tail : (Condition.walkOfEval p.toCondition w_tail b1' b2 hb).IsReduced
      · -- Tail is reduced, full walk is not: apply split_word_at_inverse + cancel_inverse_pair_eval
        obtain ⟨w_fix, w_rest, hsplit, hfix⟩ :=
          split_word_at_inverse w_tail hla_b hb1_eq hb hWred_tail hWred
        -- Use w_rest as the shorter word. We need:
        --   (1) evalWord p w_rest b1 = some b2
        --   (2) evalWord p w_rest a = some c
        --   (3) length(walkOfEval w_rest b1 b2) + 2 ≤ length(walkOfEval (l :: w_tail) b1 b2)
        -- Reformulate hb_orig and ha_orig using hsplit.
        have hb_split : evalWord (↑p) (l :: w_fix ++ [l⁻¹] ++ w_rest) b1 = some b2 := by
          rw [show (l :: w_fix ++ [l⁻¹] ++ w_rest : Word) = l :: (w_fix ++ [l⁻¹] ++ w_rest)
              from rfl, ← hsplit]; exact hb_orig
        have ha_split : evalWord (↑p) (l :: w_fix ++ [l⁻¹] ++ w_rest) a = some c := by
          rw [show (l :: w_fix ++ [l⁻¹] ++ w_rest : Word) = l :: (w_fix ++ [l⁻¹] ++ w_rest)
              from rfl, ← hsplit]; exact ha_orig
        -- Apply cancel_inverse_pair_eval to extract evalWord p w_rest a = some c.
        have ha_rest : evalWord (↑p) w_rest a = some c :=
          cancel_inverse_pair_eval hab hla_b hb1_eq hfix ha_split
        -- Apply cancel_inverse_pair_eval again at b1 to get evalWord p w_rest b1 = some b2.
        -- (Trivially b1 ≤ b1, and the fixing letters fix b1' — same statement.)
        have hb_rest : evalWord (↑p) w_rest b1 = some b2 :=
          cancel_inverse_pair_eval le_rfl hla_b hb1_eq hfix hb_split
        refine ⟨w_rest, hb_rest, ha_rest, ?_⟩
        -- Length: full walk has length ≥ length(w_rest walk) + 2 since the prefix
        -- l :: w_fix ++ [l⁻¹] adds ≥ 2 to walk length (l: b1→b1', l⁻¹: b1'→b1).
        have hlen_old : (Condition.walkOfEval p.toCondition (l :: w_tail) b1 b2 hb_orig).length =
            (Condition.walkOfEval p.toCondition w_tail b1' b2 hb).length + 1 := by
          rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_length]
          simp [hb1_eq]
        -- We need: length(walkOfEval w_rest b1 b2) + 2 ≤ length(walkOfEval w_tail b1' b2) + 1
        -- i.e., length(w_rest walk) + 1 ≤ length(w_tail walk).
        -- Since w_tail = w_fix ++ [l⁻¹] ++ w_rest, and l⁻¹ moves b1' → b1 (nonzero step)
        -- and then w_rest is a walk b1→b2, walk length ≥ 1 + length(w_rest walk).
        suffices hlen_tail :
            (Condition.walkOfEval p.toCondition w_rest b1 b2 hb_rest).length + 1 ≤
            (Condition.walkOfEval p.toCondition w_tail b1' b2 hb).length by
          rw [hlen_old]; omega
        -- Decompose w_tail = w_fix ++ [l⁻¹] ++ w_rest using a helper lemma.
        -- Prove by induction over w_fix: w_fix-letters fix b1', so they don't add walk length.
        -- The [l⁻¹] step moves b1' → b1, adding exactly 1.
        -- The remainder w_rest contributes its walk length at b1.
        clear ha_orig ha ha_split hb_split ha_rest
        subst hsplit
        -- Goal: ∃ length of walk of (w_fix ++ [l⁻¹] ++ w_rest) at b1' ≥ length at b1 of w_rest + 1
        -- Generalize over the proof; show by induction on w_fix.
        have key : ∀ (w_fix : Word) (_ : ∀ l' ∈ w_fix, evalLetter (↑p) l' b1' = some b1')
            (hb : evalWord (↑p) (w_fix ++ [l⁻¹] ++ w_rest) b1' = some b2)
            (hb_rest : evalWord (↑p) w_rest b1 = some b2),
            (Condition.walkOfEval p.toCondition w_rest b1 b2 hb_rest).length + 1 ≤
            (Condition.walkOfEval p.toCondition (w_fix ++ [l⁻¹] ++ w_rest) b1' b2 hb).length := by
          intro w_fix
          induction w_fix with
          | nil =>
            intro _ hb hb_rest
            -- evalLetter p l⁻¹ b1' = some b1 by evalLetter_letterInv
            have hlinv_b : evalLetter (↑p) l⁻¹ b1' = some b1 :=
              evalLetter_letterInv p.toCondition l b1 b1' hla_b
            -- [] ++ [l⁻¹] ++ w_rest is definitionally l⁻¹ :: w_rest (via simp normalization)
            -- Reinterpret hb at the simplified form.
            have hb' : evalWord (↑p) (l⁻¹ :: w_rest) b1' = some b2 := by
              have := hb; simp only [List.nil_append] at this; exact this
            -- Length equality between the two forms.
            have hlen_eq :
                (Condition.walkOfEval p.toCondition ([] ++ [l⁻¹] ++ w_rest) b1' b2 hb).length =
                (Condition.walkOfEval p.toCondition (l⁻¹ :: w_rest) b1' b2 hb').length := by
              congr 1
            rw [hlen_eq, Condition.walkOfEval_cons_eq _ hlinv_b,
                Condition.walkOfEvalStep_length]
            simp [Ne.symm hb1_eq]
          | cons l1 w_fix' ih_fix =>
            intro hfix hb hb_rest
            have hfix_b : evalLetter (↑p) l1 b1' = some b1' :=
              hfix l1 List.mem_cons_self
            -- (l1 :: w_fix') ++ [l⁻¹] ++ w_rest = l1 :: (w_fix' ++ [l⁻¹] ++ w_rest)
            have hb' : evalWord (↑p) (l1 :: (w_fix' ++ [l⁻¹] ++ w_rest)) b1' = some b2 := by
              have := hb; simp only [List.cons_append] at this; exact this
            have hb_tail : evalWord (↑p) (w_fix' ++ [l⁻¹] ++ w_rest) b1' = some b2 := by
              simpa [evalWord, hfix_b] using hb'
            -- The walks for the two forms are equal because the list expressions are equal.
            have hlen_eq :
                (Condition.walkOfEval p.toCondition (l1 :: w_fix' ++ [l⁻¹] ++ w_rest)
                  b1' b2 hb).length =
                (Condition.walkOfEval p.toCondition (l1 :: (w_fix' ++ [l⁻¹] ++ w_rest))
                  b1' b2 hb').length := by
              congr 1
            rw [hlen_eq, Condition.walkOfEval_cons_eq _ hfix_b,
                Condition.walkOfEvalStep_fix]
            exact ih_fix (fun l' hl' => hfix l' (List.mem_cons.mpr (Or.inr hl'))) hb_tail hb_rest
        exact key w_fix hfix hb hb_rest
      · obtain ⟨w'_tail, hb'_tail, ha'_tail, hlen'_tail⟩ :=
          ih_w a' b1' b2 c ha'_le hb ha hWred_tail
        refine ⟨l :: w'_tail, by simp [evalWord, hla_b, hb'_tail],
                               by simp [evalWord, hla_a, ha'_tail], ?_⟩
        have hlen_new : (Condition.walkOfEval p.toCondition (l :: w'_tail) b1 b2
            (by simp [evalWord, hla_b, hb'_tail])).length =
            (Condition.walkOfEval p.toCondition w'_tail b1' b2 hb'_tail).length + 1 := by
          rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_length]
          simp [hb1_eq]
        have hlen_old : (Condition.walkOfEval p.toCondition (l :: w_tail) b1 b2 hb_orig).length =
            (Condition.walkOfEval p.toCondition w_tail b1' b2 hb).length + 1 := by
          rw [Condition.walkOfEval_cons_eq _ hla_b, Condition.walkOfEvalStep_length]
          simp [hb1_eq]
        omega

/-- Inductive helper for `evalWord_fixing`: closes the fixing property by structural
    recursion on the walk-length bound `n`. -/
private lemma evalWord_fixing_aux :
    ∀ (n : ℕ) (w : Word) (p : KnightCondition) (a b c : ℚ),
      a ≤ b → (hb : evalWord (↑p) w b = some b) → evalWord (↑p) w a = some c →
      (Condition.walkOfEval p.toCondition w b b hb).length ≤ n → a = c
  | 0, w, p, a, b, c, hab, hb, ha, hlen => by
      have hnil : Condition.walkOfEval p.toCondition w b b hb = .nil :=
        SimpleGraph.Walk.Nil.eq_nil (SimpleGraph.Walk.length_eq_zero_iff.mp (Nat.le_zero.mp hlen))
      exact (evalWord_fixes_of_all_fix_b hab (allLettersFix_of_nil_walk hb hnil) ha).symm
  | n + 1, w, p, a, b, c, hab, hb, ha, hlen => by
      by_cases hWnil : Condition.walkOfEval p.toCondition w b b hb = .nil
      · exact (evalWord_fixes_of_all_fix_b hab (allLettersFix_of_nil_walk hb hWnil) ha).symm
      · by_cases hWred : (Condition.walkOfEval p.toCondition w b b hb).IsReduced
        · exact absurd (SimpleGraph.IsAcyclic.nil_of_isReduced_closed p.acyclic _ hWred) hWnil
        · obtain ⟨w', hb', ha', hlen'⟩ :=
            shorten_non_reduced_walk p w a b b c hab hb ha hWred
          exact evalWord_fixing_aux n w' p a b c hab hb' ha' (by omega)

/-- Key fixing property: if `evalWord p w b = some b` and `a ≤ b`,
    then `evalWord p w a = some a`. -/
lemma evalWord_fixing (w : Word) (p : KnightCondition) (a b c : ℚ)
    (hab : a ≤ b)
    (hevalb : evalWord p w b = some b) (hevala : evalWord p w a = some c) : a = c :=
  evalWord_fixing_aux _ w p a b c hab hevalb hevala le_rfl

end KnightCondition
