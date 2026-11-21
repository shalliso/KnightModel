import KnightModel.RankTwo.WordIntervalFormula

/-! # Semilinearity of normalized interval coordinates

Matching endpoint heads are removed recursively. Their common letter is
prepended to the output. At unequal heads, use the interval construction.
-/

namespace KnightModel.RankTwo.Semilinear

open Word Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V]
variable (d : Letter V) (hd : (⟨0, le_rfl⟩ : Letter V) < d)

def rawHGraph : List V → List V → List V → List V → Prop
  | [], _, _, _ => False
  | a :: v, [], x, y => rawIntervalGraph d hd (a :: v) [] x y
  | a :: v, b :: u, x, y => if a = b then
      match y with
      | [] => False
      | c :: z => 0 ≤ a ∧ a = c ∧ rawHGraph v u x z
    else rawIntervalGraph d hd (a :: v) (b :: u) x y

private theorem rawH_cons (a b : V) (v u x y : List V) :
    rawHGraph d hd (a :: v) (b :: u) x y =
    (if a = b then match y with
      | [] => False
      | c :: z => 0 ≤ a ∧ a = c ∧ rawHGraph d hd v u x z
    else rawIntervalGraph d hd (a :: v) (b :: u) x y) := rfl

private abbrev actualH := HGraph shiftLetter (⟨0, le_rfl⟩ : Letter V) d hd shiftOpenLetter

private theorem h_interval_of_same_action (v u x y : Word (Letter V))
    (he : ∀ h : v < u, H shiftLetter (⟨0, le_rfl⟩ : Letter V) d hd shiftOpenLetter v u h =
      intervalIso shiftLetter ⟨0, le_rfl⟩ d hd shiftOpenLetter h) :
    actualH d hd v u x y ↔ letterIntervalGraph d hd v u x y := by
  constructor
  · rintro ⟨h,z,hx,hy⟩
    exact ⟨h,z,hx,he h ▸ hy⟩
  · rintro ⟨h,z,hx,hy⟩
    exact ⟨h,z,hx,(he h).symm ▸ hy⟩

private theorem hCommon (a : Letter V) (v u x y : Word (Letter V)) :
    actualH d hd (cons a v) (cons a u) x y ↔
    ∃ t : Word (Letter V), actualH d hd v u x t ∧ cons a t = y :=
  Word.hgraph_common (A := Letter V) (shiftLetter (V := V)) (⟨0, le_rfl⟩ : Letter V) d hd
    (shiftOpenLetter (V := V)) a v u x y

/-- Correctness on the actual nonnegative alphabet. -/
theorem rawHGraph_map (v u x y : Word (Letter V)) :
    rawHGraph d hd (List.map Subtype.val v) (List.map Subtype.val u)
      (List.map Subtype.val x) (List.map Subtype.val y) ↔
    HGraph shiftLetter (⟨0,le_rfl⟩ : Letter V) d hd shiftOpenLetter v u x y := by
  induction v generalizing u y with
  | nil =>
    exact ⟨False.elim, fun ⟨h,_⟩ => (le_root u).not_gt h⟩
  | cons a v ih =>
    cases u with
    | nil =>
      exact (rawIntervalGraph_map d hd (cons a v) root x y).trans
        (h_interval_of_same_action d hd (cons a v) root x y
          (H_at_root _ _ _ _ _ _)).symm
    | cons b u =>
      by_cases he : a = b
      · subst b
        change rawHGraph d hd (a.val :: _) (a.val :: _) _ _ ↔ _
        rw [rawH_cons, if_pos rfl]
        refine Iff.trans ?_ (hCommon d hd a v u x y).symm
        cases y with
        | nil =>
          exact ⟨False.elim, fun ⟨_, _, e⟩ => by cases e⟩
        | cons c y =>
          constructor
          · rintro ⟨_, ec, h⟩
            exact ⟨y, (ih u y).mp h, congrArg (fun m => Word.cons m y) (Subtype.ext ec)⟩
          · rintro ⟨z, h, ey⟩
            obtain ⟨rfl, rfl⟩ := List.cons.inj ey
            exact ⟨a.property, rfl, (ih u z).mpr h⟩
      · change rawHGraph d hd (a.val :: _) (b.val :: _) _ _ ↔ _
        rw [rawH_cons,
            if_neg (show a.val ≠ b.val from fun e => he (Subtype.ext e))]
        exact (rawIntervalGraph_map d hd (cons a v) (cons b u) x y).trans
          (h_interval_of_same_action d hd _ _ x y
            (fun h => H_different _ _ _ _ _ a b v u h he)).symm

/-- Semilinearity of the normalized interval graph, with all four word
shapes fixed and arbitrary affine substitutions for their coordinates. -/
theorem def_rawHGraph_of_interval
    (defI : ∀ {k} (v u x y : List (Term V k)), Definable {p |
      rawIntervalGraph d hd (evalWord v p) (evalWord u p) (evalWord x p) (evalWord y p)})
    {k} (v u x y : List (Term V k)) : Definable {p |
      rawHGraph d hd (evalWord v p) (evalWord u p) (evalWord x p) (evalWord y p)} := by
  induction v generalizing u y with
  | nil => exact def_word_false
  | cons a v ih =>
    cases u with
    | nil => exact defI (a :: v) [] x y
    | cons b u =>
      have hi := defI (a :: v) (b :: u) x y
      have eq := def_term_eq a b
      cases y with
      | nil =>
        convert eq.compl.inter hi using 1
        ext p
        simp only [mem_setOf_eq, mem_inter_iff, mem_compl_iff, evalWord, List.map_cons,
          List.map_nil, rawH_cons]
        by_cases h : a.eval p = b.eval p <;> simp [h]
      | cons c y =>
        have same := (def_term_le (.const 0) a).inter ((def_term_eq a c).inter (ih u y))
        convert (eq.inter same).union (eq.compl.inter hi) using 1
        ext p
        simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff, evalWord,
          List.map_cons, rawH_cons, Term.eval]
        by_cases h : a.eval p = b.eval p <;> simp [h]

/-- Eliminate both the finite-word quantifiers and all scalar comparisons
in the normalized interval graph. -/
theorem def_rawHGraph (qe : HeadElimination V) (d : Letter V)
    (hd : (⟨0, le_rfl⟩ : Letter V) < d) {k} (v u x y : List (Term V k)) :
    Definable {p | rawHGraph d hd (evalWord v p) (evalWord u p) (evalWord x p) (evalWord y p)} :=
  def_rawHGraph_of_interval d hd (def_rawIntervalGraph qe d hd) v u x y

end KnightModel.RankTwo.Semilinear
