/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.Condition
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! ## The Evaluation Graph of a Condition

We model the evaluation structure of a `Condition` as an undirected simple graph
(`EvalGraph`) and use graph-theoretic acyclicity to characterize the combined
`Faithful + IsAcyclic` condition and prove it is preserved under `CanExtend` extensions.

## Main definitions
- `Condition.EvalGraph`: undirected simple graph on ℚ, edge {a,b} iff some letter evaluates a→b

## Main results
- `isAcyclic_of_canExtend`: faithful + acyclic is preserved under `CanExtend` (acyclicity part)
- `faithful_of_canExtend`: faithful + acyclic is preserved under `CanExtend` (faithfulness part)
- `evalGraph_inv_condition_eq`: the EvalGraph of `Condition.inv p` equals that of `p`

## Tags
knight, condition, evaluation, graph, acyclic
-/

/-! ### EvalGraph definition -/

/-- The evaluation graph of a condition: vertices are elements of ℚ, and there is an
    edge between `a` and `b` (with `a ≠ b`) iff some letter evaluates `a` to `b`. -/
noncomputable def Condition.EvalGraph (p : Condition) : SimpleGraph ℚ where
  Adj a b := a ≠ b ∧ ∃ l : Letter, evalLetter p l a = some b
  symm := ⟨fun a b ⟨hne, l, hl⟩ => ⟨hne.symm, l⁻¹, evalLetter_letterInv p l a b hl⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

@[simp]
lemma Condition.evalGraph_adj_iff (p : Condition) (a b : ℚ) :
    (p.EvalGraph).Adj a b ↔ a ≠ b ∧ ∃ l : Letter, evalLetter p l a = some b := Iff.rfl

/-! ### Reachability corresponds to evalWord -/

lemma exists_evalWord_of_reachable (p : Condition) {a b : ℚ}
    (h : (p.EvalGraph).Reachable a b) : ∃ w : Word, evalWord p w a = some b := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact ⟨[], by simp [evalWord]⟩
  | cons hadj _ ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨hne, l, hl⟩ := p.evalGraph_adj_iff _ _ |>.mp hadj
    exact ⟨l :: w, by simp [evalWord, hl, hw]⟩

/-! ### Extension graph lemmas -/

/-- When `a ≠ b`, extending by `(a, b)` at index `n` adds exactly the edge `{a, b}`. -/
lemma evalGraph_extension_eq_sup {p : Condition} {n : ℕ} {a b : ℚ} (hab : a ≠ b)
    (p' : p.Extension n a b) :
    p'.toCondition.EvalGraph = p.EvalGraph ⊔ SimpleGraph.fromEdgeSet {s(a, b)} := by
  ext x y
  simp only [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
    Condition.evalGraph_adj_iff]
  constructor
  · rintro ⟨hne, l, hl⟩
    by_cases h_old : evalLetter p l x = some y
    · exact Or.inl ⟨hne, l, h_old⟩
    · have hl_none := evalLetter_none_of_ext_ne p' hl h_old
      rcases new_edge_of_evalLetter_diff p' hl hl_none with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · exact Or.inr ⟨Sym2.eq_iff.mpr (Or.inl ⟨rfl, rfl⟩), hne⟩
      · exact Or.inr ⟨Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩), hne⟩
  · rintro (⟨hne, l, hl⟩ | ⟨hsym, hne⟩)
    · exact ⟨hne, l, evalLetter_eq_of_extension p' hl⟩
    · rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne, (n, false), evalLetter_extension_fwd p'⟩
      · exact ⟨hne, (n, true), evalLetter_extension_inv p'⟩

/-- Extending by `(a, a)` does not change the evaluation graph. -/
lemma evalGraph_eq_of_extension_self {p : Condition} {n : ℕ} {a : ℚ}
    (p' : p.Extension n a a) :
    p'.toCondition.EvalGraph = p.EvalGraph := by
  ext x y
  simp only [Condition.evalGraph_adj_iff]
  constructor
  · rintro ⟨hne, l, hl⟩
    refine ⟨hne, l, ?_⟩
    by_contra h
    have hl_none := evalLetter_none_of_ext_ne p' hl h
    rcases new_edge_of_evalLetter_diff p' hl hl_none with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact hne rfl
    · exact hne rfl
  · rintro ⟨hne, l, hl⟩
    exact ⟨hne, l, evalLetter_eq_of_extension p' hl⟩

/-! ### Walk induced by a word -/

/-- Auxiliary: build a walk from a letter evaluation and a tail walk.
    If the letter fixes the vertex, skip it; otherwise add an edge. -/
noncomputable def Condition.walkOfEvalStep (p : Condition) (l : Letter) (a c b : ℚ)
    (hla : evalLetter p l a = some c) (tail : p.EvalGraph.Walk c b) : p.EvalGraph.Walk a b :=
  if hac : a = c then hac ▸ tail
  else .cons (p.evalGraph_adj_iff a c |>.mpr ⟨hac, l, hla⟩) tail

/-- Extract the tail evaluation proof from a cons word evaluation. -/
private lemma evalWord_tail_of_evalLetter {p : Condition} {l : Letter} {w : Word} {a b c : ℚ}
    (h : evalWord p (l :: w) a = some b) (hla : evalLetter p l a = some c) :
    evalWord p w c = some b := by
  simp only [evalWord, hla, Option.bind_some] at h; exact h

/-- Helper for the cons case: dispatch on the option value using `match`. -/
private noncomputable def walkOfEval_option (p : Condition) (l : Letter) (w : Word)
    (a b : ℚ) (h : evalWord p (l :: w) a = some b)
    (rec : ∀ (c : ℚ), evalWord p w c = some b → p.EvalGraph.Walk c b) :
    (o : Option ℚ) → (evalLetter p l a = o) → p.EvalGraph.Walk a b
  | none, hla => absurd h (by simp [evalWord, hla])
  | some c, hla => p.walkOfEvalStep l a c b hla
      (rec c (evalWord_tail_of_evalLetter h hla))

/-- Convert a successful word evaluation into a Walk in the EvalGraph.
    Letters that fix the current vertex are skipped (no edge added); letters that
    strictly move it contribute one edge. -/
noncomputable def Condition.walkOfEval (p : Condition) :
    ∀ (w : Word) (a b : ℚ), evalWord p w a = some b → p.EvalGraph.Walk a b
  | [], _, _, h => by simp only [evalWord, Option.some.injEq] at h; subst h; exact .nil
  | l :: w, a, b, h =>
      walkOfEval_option p l w a b h
        (fun c hw => Condition.walkOfEval p w c b hw)
        (evalLetter p l a) rfl

/-- `walkOfEval` for a cons word equals `walkOfEvalStep` applied to the actual letter value. -/
lemma Condition.walkOfEval_cons_eq {p : Condition} {l : Letter} {w : Word} {a b c : ℚ}
    (h : evalWord p (l :: w) a = some b) (hla : evalLetter p l a = some c) :
    Condition.walkOfEval p (l :: w) a b h =
      p.walkOfEvalStep l a c b hla
        (Condition.walkOfEval p w c b (evalWord_tail_of_evalLetter h hla)) := by
  -- walkOfEval_option is defined by matching on its Option argument.
  -- We show it's defeq to the RHS by generalizing over the option and its proof.
  suffices ∀ (o : Option ℚ) (ho : evalLetter p l a = o) (hsome : o = some c),
      walkOfEval_option p l w a b h
        (fun d hw => Condition.walkOfEval p w d b hw) o ho =
      p.walkOfEvalStep l a c b (ho.trans hsome)
          (Condition.walkOfEval p w c b
            (evalWord_tail_of_evalLetter h (ho.trans hsome))) by
    exact this (evalLetter p l a) rfl hla
  intro o ho hsome
  subst hsome
  rfl

/-! ### Walk API -/

@[simp]
lemma Condition.walkOfEval_nil (p : Condition) (a : ℚ) (h : evalWord p [] a = some a) :
    Condition.walkOfEval p [] a a h = .nil := rfl

/-! ### Walk reduction theory -/

/-- A walk is *reduced* (no adjacent backtrack): inductively defined so that
    `nil` and single-edge walks are always reduced, and `cons h₁ (cons h₂ rest)` is reduced
    iff the start vertex `u` ≠ the vertex `w` after two steps, and the tail is reduced. -/
inductive SimpleGraph.Walk.IsReduced {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V}, G.Walk u v → Prop where
  | nil {v} : IsReduced (SimpleGraph.Walk.nil : G.Walk v v)
  | cons_nil {u v} (h : G.Adj u v) : IsReduced (Walk.cons h Walk.nil)
  | cons_cons {u v w x} (h1 : G.Adj u v) (h2 : G.Adj v w) (rest : G.Walk w x)
      (hne : u ≠ w) (htail : IsReduced (Walk.cons h2 rest)) :
      IsReduced (Walk.cons h1 (Walk.cons h2 rest))

@[simp]
lemma SimpleGraph.Walk.isReduced_nil_iff {V : Type*} {G : SimpleGraph V} {v : V} :
    (SimpleGraph.Walk.nil : G.Walk v v).IsReduced ↔ True :=
  ⟨fun _ => trivial, fun _ => .nil⟩

@[simp]
lemma SimpleGraph.Walk.isReduced_cons_nil_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) : (Walk.cons h Walk.nil).IsReduced ↔ True :=
  ⟨fun _ => trivial, fun _ => .cons_nil h⟩

@[simp]
lemma SimpleGraph.Walk.isReduced_cons_cons_iff {V : Type*} {G : SimpleGraph V}
    {u v w x : V} (h1 : G.Adj u v) (h2 : G.Adj v w) (rest : G.Walk w x) :
    (Walk.cons h1 (Walk.cons h2 rest)).IsReduced ↔
    u ≠ w ∧ (Walk.cons h2 rest).IsReduced :=
  ⟨fun hred => by cases hred with | cons_cons _ _ _ hne htail => exact ⟨hne, htail⟩,
   fun ⟨hne, htail⟩ => .cons_cons h1 h2 rest hne htail⟩

/-- The tail of a reduced walk is reduced. -/
lemma SimpleGraph.Walk.IsReduced.tail {V : Type*} {G : SimpleGraph V} {u v w : V}
    (h : G.Adj u v) (rest : G.Walk v w)
    (hred : (Walk.cons h rest).IsReduced) : rest.IsReduced := by
  cases hred with
  | cons_nil => exact .nil
  | cons_cons _ _ _ _ htail => exact htail

/-- A reduced walk in an acyclic graph is a trail (no repeated edges). -/
private lemma isTrail_of_isReduced_of_isAcyclic {V : Type*} {G : SimpleGraph V}
    (hacyc : G.IsAcyclic) {u v : V} {W : G.Walk u v}
    (hred : W.IsReduced) : W.IsTrail := by
  induction hred with
  | nil => exact SimpleGraph.Walk.IsTrail.nil
  | cons_nil h => exact ⟨by simp⟩
  | cons_cons h1' h2' rest' hne' _ ih_tail =>
    -- By IH, the tail is a trail, hence a path by isPath_iff_isTrail
    have htail_trail := ih_tail
    have htail_path := (hacyc.isPath_iff_isTrail _).mpr htail_trail
    -- The first vertex of the tail is not in the rest of the support
    have hnodup := htail_path.support_nodup
    rw [SimpleGraph.Walk.support_cons] at hnodup
    have hv'_not_in := (List.nodup_cons.mp hnodup).1
    -- Build the trail proof for the full walk
    constructor
    -- Need: edges of (cons h1' (cons h2' rest')) are nodup
    simp only [SimpleGraph.Walk.edges_cons]
    rw [List.nodup_cons]
    refine ⟨?_, htail_trail.edges_nodup⟩
    -- Need: leading edge not in tail's edges
    intro hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hmem_eq | hmem_rest
    · -- Leading edge equals second edge: contradicts hne' or loopless
      rw [Sym2.eq_iff] at hmem_eq
      rcases hmem_eq with ⟨h_eq1, h_eq2⟩ | ⟨h_eq1, h_eq2⟩
      · -- u = v and v = w: u = v contradicts Adj u v (loopless)
        exact absurd (h_eq1 ▸ h1') (G.loopless.irrefl _)
      · -- u = w and v = v: contradicts hne' : u ≠ w
        exact absurd h_eq1 hne'
    · -- Leading edge in rest's edges: the second vertex appears in rest's support,
      -- contradicting path nodup
      exact hv'_not_in (SimpleGraph.Walk.snd_mem_support_of_mem_edges rest' hmem_rest)

/-- In an acyclic simple graph, any closed reduced walk is nil. -/
lemma SimpleGraph.IsAcyclic.nil_of_isReduced_closed {V : Type*} {G : SimpleGraph V}
    (hacyc : G.IsAcyclic) {v : V} (W : G.Walk v v)
    (hred : W.IsReduced) : W = .nil := by
  -- A reduced walk in an acyclic graph is a trail, hence a path.
  have htrail := isTrail_of_isReduced_of_isAcyclic hacyc hred
  have hpath := (hacyc.isPath_iff_isTrail W).mpr htrail
  -- A closed path must be nil: if non-nil, the first vertex appears twice in support.
  cases W with
  | nil => rfl
  | cons hadj tail =>
    exfalso
    have hnodup := hpath.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at hnodup
    exact hnodup.1 tail.end_mem_support

lemma Condition.walkOfEvalStep_fix {p : Condition} {l : Letter} {a b : ℚ}
    (hla : evalLetter p l a = some a) (tail : p.EvalGraph.Walk a b) :
    p.walkOfEvalStep l a a b hla tail = tail := by
  simp [Condition.walkOfEvalStep]

lemma Condition.walkOfEvalStep_move {p : Condition} {l : Letter} {a c b : ℚ}
    (hla : evalLetter p l a = some c) (hac : a ≠ c) (tail : p.EvalGraph.Walk c b) :
    p.walkOfEvalStep l a c b hla tail =
      .cons (p.evalGraph_adj_iff a c |>.mpr ⟨hac, l, hla⟩) tail := by
  simp [Condition.walkOfEvalStep, hac]

lemma Condition.walkOfEvalStep_length {p : Condition} {l : Letter} {a c b : ℚ}
    (hla : evalLetter p l a = some c) (tail : p.EvalGraph.Walk c b) :
    (p.walkOfEvalStep l a c b hla tail).length =
      if a = c then tail.length else tail.length + 1 := by
  by_cases hac : a = c
  · subst hac; simp [Condition.walkOfEvalStep]
  · simp [Condition.walkOfEvalStep, hac]

/-- The walk for a cons word has length at least 1 when the head letter moves
    the vertex. This is proved by induction using the structure of walkOfEval. -/
lemma Condition.walkOfEval_cons_length_pos {p : Condition} {l : Letter} {w : Word}
    {a c b : ℚ} (h : evalWord p (l :: w) a = some b)
    (hla : evalLetter p l a = some c) (hac : a ≠ c) :
    (Condition.walkOfEval p (l :: w) a b h).length ≥ 1 := by
  rw [Condition.walkOfEval_cons_eq h hla,
      Condition.walkOfEvalStep_length hla]
  simp [hac]



/-! ### noNewCycles implies non-reachability -/

lemma not_reachable_of_noNewCycles {p : Condition} {a b : ℚ}
    (h : ∀ w : Word, evalWord p w a ≠ some b) :
    ¬ (p.EvalGraph).Reachable a b := by
  intro hreach
  obtain ⟨w, hw⟩ := exists_evalWord_of_reachable p hreach
  exact h w hw

/-! ### Clean public API for CanExtend -/

/-- Extending a faithful, acyclic condition by a `CanExtend` pair preserves acyclicity. -/
theorem isAcyclic_of_canExtend {p : Condition} {n : ℕ} {a b : ℚ}
    (hcanext : p.CanExtend n a b)
    (hnew : a = b ∨ ∀ w : Word, evalWord p w a ≠ some b)
    (_hfaith : p.Faithful) (hacyc : p.EvalGraph.IsAcyclic) :
    hcanext.toExtension.toCondition.EvalGraph.IsAcyclic := by
  rcases hnew with rfl | h_no
  · exact evalGraph_eq_of_extension_self hcanext.toExtension ▸ hacyc
  · have hab : a ≠ b := by
      intro h; subst h; exact absurd rfl (h_no [])
    have hreach : ¬ p.EvalGraph.Reachable a b := not_reachable_of_noNewCycles h_no
    rw [evalGraph_extension_eq_sup hab hcanext.toExtension]
    exact (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable a b hreach).mpr hacyc

/-- Extending a faithful, acyclic condition by a `CanExtend` pair preserves faithfulness. -/
theorem faithful_of_canExtend {p : Condition} {n : ℕ} {a b : ℚ}
    (hcanext : p.CanExtend n a b)
    (hnew : a = b ∨ ∀ w : Word, evalWord p w a ≠ some b)
    (hfaith : p.Faithful) (_hacyc : p.EvalGraph.IsAcyclic) :
    hcanext.toExtension.toCondition.Faithful :=
  Condition.faithful_extension hfaith hnew hcanext.toExtension

/-- The evaluation graph of `p⁻¹` is identical to that of `p`. -/
lemma evalGraph_inv_condition_eq (p : Condition) :
    (p⁻¹).EvalGraph = p.EvalGraph := by
  ext a b
  simp only [Condition.evalGraph_adj_iff, evalLetter_inv_condition]
  constructor
  · rintro ⟨hne, l, hl⟩
    exact ⟨hne, l⁻¹, hl⟩
  · rintro ⟨hne, l, hl⟩
    exact ⟨hne, l⁻¹, by rw [inv_inv]; exact hl⟩
