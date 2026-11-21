import KnightModel.RankTwo.ProgramDefinabilitySelection
import KnightModel.RankTwo.WordEvaluation

/-! # Fixed-length semilinear tests on words over a nonnegative alphabet

The ambient variables are arbitrary ordered vectors. A raw word belongs to
the alphabet precisely when all its coordinates are nonnegative.
-/

namespace KnightModel.RankTwo.Semilinear

open Word Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {k : ℕ}

/-- Constant Boolean tests, including the two empty-word base cases. -/
theorem def_word_false : Definable {p : Fin k → V | False} :=
  ⟨.ltZero (.const 0), fun _ => ⟨False.elim, lt_irrefl _⟩⟩

theorem def_word_true : Definable {p : Fin k → V | True} := by
  simpa only [Set.compl_setOf, not_false_eq_true] using
    (def_word_false (k := k) (V := V)).compl

theorem def_term_lt (a b : Term V k) : Definable {p | a.eval p < b.eval p} := by
  refine ⟨.ltZero (.add a (.scale (-1) b)), fun p => ?_⟩
  change a.eval p < b.eval p ↔ a.eval p + (-1 : ℚ) • b.eval p < 0
  rw [neg_one_smul, ← sub_eq_add_neg, sub_neg]

theorem def_term_le (a b : Term V k) : Definable {p | a.eval p ≤ b.eval p} := by
  simpa only [Set.compl_setOf, not_lt] using (def_term_lt b a).compl

theorem def_term_eq (a b : Term V k) : Definable {p | a.eval p = b.eval p} := by
  convert (def_term_le a b).inter (def_term_le b a) using 1
  ext p
  exact le_antisymm_iff

theorem def_word_nonneg (w : List (Term V k)) :
    Definable {p | ∀ v ∈ evalWord w p, 0 ≤ v} := by
  induction w with
  | nil => simpa [evalWord] using (def_word_true (k := k) (V := V))
  | cons a w ih =>
    convert (def_term_le (.const 0) a).inter ih using 1
    ext p
    simp [evalWord, Term.eval]

theorem def_word_eq (x y : List (Term V k)) :
    Definable {p | evalWord x p = evalWord y p} := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simpa [evalWord] using (def_word_true (k := k) (V := V))
    | cons b y => simpa [evalWord] using (def_word_false (k := k) (V := V))
  | cons a x ih =>
    cases y with
    | nil => simpa [evalWord] using (def_word_false (k := k) (V := V))
    | cons b y =>
      convert (def_term_eq a b).inter (ih y) using 1
      ext p
      simp [evalWord]

/-- Here the order on the word type has the root as its greatest element. -/
theorem def_word_lt (x y : List (Term V k)) :
    Definable {p | @LT.lt (Word V) ((inferInstance : LinearOrder (Word V)).toLT) (evalWord x p) (evalWord y p)} := by
  induction x generalizing y with
  | nil =>
    convert (def_word_false (k := k) (V := V)) using 1
    ext p
    exact ⟨(Word.le_root (evalWord y p : Word V)).not_gt, False.elim⟩
  | cons a x ih =>
    cases y with
    | nil =>
      convert (def_word_true (k := k) (V := V)) using 1
      ext p
      exact ⟨fun _ => trivial, fun _ => Word.cons_lt_root (a.eval p) (evalWord x p)⟩
    | cons b y =>
      convert (def_term_lt a b).union ((def_term_eq a b).inter (ih y)) using 1
      ext p
      exact Word.cons_lt_cons_iff (a := a.eval p) (b := b.eval p)
        (u := evalWord x p) (v := evalWord y p)

theorem def_word_le (x y : List (Term V k)) :
    Definable {p | @LE.le (Word V) ((inferInstance : LinearOrder (Word V)).toLE) (evalWord x p) (evalWord y p)} := by
  simpa only [Set.compl_setOf, not_lt] using (def_word_lt y x).compl

theorem def_word_prepend (s x y : List (Term V k)) :
    Definable {p | (Word.prepend (evalWord s p) (evalWord x p) : Word V) = evalWord y p} := by
  convert def_word_eq (s ++ x) y using 1
  ext p
  simp only [mem_setOf_eq, evalWord, List.map_append, Word.prepend]
  rfl

omit [Module ℚ V] [IsOrderedAddMonoid V] in
/-- Coercion of all letters to the ambient group preserves the order in which
the root is greatest. -/
theorem word_map_val_lt (u v : Word (Letter V)) :
    @LT.lt (Word V) inferInstance (List.map Subtype.val u) (List.map Subtype.val v) ↔ u < v := by
  induction u generalizing v with
  | nil =>
    exact ⟨fun h => ((Word.le_root (List.map Subtype.val v : Word V)).not_gt h).elim,
      fun h => ((Word.le_root v).not_gt h).elim⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨fun _ => Word.cons_lt_root a u, fun _ => Word.cons_lt_root a.val _⟩
    | cons b v =>
      change Word.cons a.val (List.map Subtype.val u) < Word.cons b.val (List.map Subtype.val v) ↔
        Word.cons a u < Word.cons b v
      rw [Word.cons_lt_cons_iff, Word.cons_lt_cons_iff, ih v, Subtype.val_inj]
      rfl

omit [Module ℚ V] [IsOrderedAddMonoid V] in
theorem word_map_val_le (u v : Word (Letter V)) :
    @LE.le (Word V) inferInstance (List.map Subtype.val u) (List.map Subtype.val v) ↔ u ≤ v :=
  le_iff_le_iff_lt_iff_lt.mpr (word_map_val_lt v u)

omit [Module ℚ V] [IsOrderedAddMonoid V] in
theorem exists_nonneg_word (w : List V) :
    (∃ v : List (Letter V), v.map Subtype.val = w) ↔ ∀ x ∈ w, 0 ≤ x := by
  constructor
  · rintro ⟨v, rfl⟩ x hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact z.property
  · intro h
    induction w with
    | nil => exact ⟨[],rfl⟩
    | cons x w ih =>
      obtain ⟨v, hv⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      exact ⟨⟨x, h x List.mem_cons_self⟩ :: v, by simp [hv]⟩

/-- The lifted single-letter open-tail graph always rejects negative parameters
and words outside the alphabet. -/
def rawSingleGraph (a : V) (x y : List V) : Prop :=
  ∃ h : 0 ≤ a, liftWordGraph Subtype.val
    (Word.SingleGraph (⟨0, le_rfl⟩ : Letter V) Word.shiftOpenLetter ⟨a,h⟩) x y

theorem rawSingleGraph_map (a : Letter V) (x y : List (Letter V)) :
    rawSingleGraph a.val (x.map Subtype.val) (y.map Subtype.val) ↔
      Word.SingleGraph (⟨0, le_rfl⟩ : Letter V) Word.shiftOpenLetter a x y := by
  constructor
  · rintro ⟨_, h⟩
    exact (liftWordGraph_map Subtype.val_injective _ x y).mp h
  · intro h
    exact ⟨a.property, (liftWordGraph_map Subtype.val_injective _ x y).mpr h⟩

theorem rawSingleGraph_nil (a : V) (y : List V) :
    rawSingleGraph a [] y ↔ 0 ≤ a ∧ y = [] := by
  constructor
  · rintro ⟨ha, u, v, hu, hv, h⟩
    obtain rfl : u = [] := List.map_eq_nil_iff.mp hu
    have h' : v = [] := (Word.singleGraph_root _ _ _ _).mp h
    exact ⟨ha, hv ▸ h' ▸ rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨ha, [], [], rfl, rfl, (Word.singleGraph_root _ _ _ _).mpr rfl⟩

theorem rawSingleGraph_cons (a t : V) (w y : List V) :
    rawSingleGraph a (t :: w) y ↔
      0 ≤ a ∧ 0 < t ∧ (∀ v ∈ w, 0 ≤ v) ∧ y = (t + a) :: w := by
  constructor
  · rintro ⟨ha, u, v, hu, hv, h⟩
    cases u with
    | nil => simp at hu
    | cons z u =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hu
      obtain ⟨hz, rfl⟩ := (Word.singleGraph_cons _ _ _ _ _ _).mp h
      exact ⟨ha, hz, (exists_nonneg_word _).mp ⟨u,rfl⟩, hv.symm⟩
  · rintro ⟨ha, ht, hw, rfl⟩
    obtain ⟨u, rfl⟩ := (exists_nonneg_word w).mpr hw
    let z : Letter V := ⟨t, ht.le⟩
    let b : Letter V := ⟨a, ha⟩
    let c := (Word.shiftOpenLetter b).symm ⟨z, ht⟩
    exact ⟨ha, z :: u, c.val :: u, rfl, rfl,
      (Word.singleGraph_cons _ _ _ _ _ _).mpr ⟨ht, rfl⟩⟩

/-- Uniform semilinearity of the open translation graph on two fixed word shapes. -/
theorem def_word_single (a : Term V k) (x y : List (Term V k)) :
    Definable {p | rawSingleGraph (a.eval p) (evalWord x p) (evalWord y p)} := by
  cases x with
  | nil =>
    convert (def_term_le (.const 0) a).inter (def_word_eq y []) using 1
    ext p
    exact rawSingleGraph_nil _ _
  | cons t w =>
    have h := (def_term_le (.const 0) a).inter ((def_term_lt (.const 0) t).inter
      ((def_word_nonneg w).inter (def_word_eq y (.add t a :: w))))
    convert h using 1
    ext p
    exact rawSingleGraph_cons _ _ _ _

end KnightModel.RankTwo.Semilinear
