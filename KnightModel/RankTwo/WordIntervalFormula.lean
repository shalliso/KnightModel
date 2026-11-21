import KnightModel.RankTwo.WordTailFormula

/-! # Fixed-shape semilinearity of interval coordinates -/

namespace KnightModel.RankTwo.Semilinear

open Word Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V]
variable (d : Letter V) (hd : (⟨0, le_rfl⟩ : Letter V) < d)

/-- An interval coordinate, with the order of the endpoints and the domain included. -/
def letterIntervalGraph (v u x y : Word (Letter V)) : Prop :=
  ∃ h : v < u, ∃ z : Ioi (cons (⟨0,le_rfl⟩ : Letter V) root), x = z.val ∧
    y = (intervalIso shiftLetter ⟨0, le_rfl⟩ d hd shiftOpenLetter h z).val

private theorem intervalForm (v u x y : Word (Letter V)) :
    letterIntervalGraph d hd v u x y ↔ v < u ∧
    ∃ t z : Word (Letter V), through shiftLetter u t = v ∧
      TailGraph shiftLetter (⟨0, le_rfl⟩ : Letter V) d hd shiftOpenLetter t x z ∧
      through shiftLetter u z = y := by
  constructor
  · rintro ⟨h, g⟩
    exact ⟨h, (Word.interval_graph _ _ _ _ _ v u h x y).mp g⟩
  · rintro ⟨h, g⟩
    exact ⟨h, (Word.interval_graph _ _ _ _ _ v u h x y).mpr g⟩

/-- A folded complementary-tail graph with its two bounded auxiliary words. -/
def rawIntervalGraph (v u x y : List V) : Prop :=
  @LT.lt (Word V) inferInstance v u ∧ ∃ t : List V, t.length ≤ v.length ∧
    ∃ z : List V, z.length ≤ y.length ∧ rawFoldGraph u t v ∧ rawTailGraph d hd t x z ∧
      rawFoldGraph u z y

private theorem fold_at_letters (u t v : List (Letter V)) :
    rawFoldGraph (u.map Subtype.val) (t.map Subtype.val) (v.map Subtype.val) ↔
    through shiftLetter u t = v := by
  constructor
  · intro h
    exact (List.map_injective_iff.mpr Subtype.val_injective) ((scalarFold_map u t).symm.trans h.2.2)
  · intro h
    exact (rawFoldGraph_iff ..).mpr ⟨u, rfl, t, v, rfl, rfl, h⟩

private theorem tail_at_letters (t x z : List (Letter V)) :
    rawTailGraph d hd (t.map Subtype.val) (x.map Subtype.val) (z.map Subtype.val) ↔
    TailGraph shiftLetter ⟨0, le_rfl⟩ d hd shiftOpenLetter t x z := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain rfl := (List.map_injective_iff.mpr Subtype.val_injective) hv
    exact (liftWordGraph_map Subtype.val_injective _ x z).mp h
  · intro h
    exact ⟨t, rfl, x, z, rfl, rfl, h⟩

/-- The vector relation represents the original interval coordinate. -/
theorem rawIntervalGraph_map (v u x y : Word (Letter V)) :
    rawIntervalGraph d hd (List.map Subtype.val v) (List.map Subtype.val u)
      (List.map Subtype.val x) (List.map Subtype.val y) ↔ letterIntervalGraph d hd v u x y := by
  rw [intervalForm]
  constructor
  · rintro ⟨hlt, t, _, z, _, htv, ht, hzy⟩
    obtain ⟨t', rfl⟩ := (exists_nonneg_word t).mpr htv.2.1
    obtain ⟨z', rfl⟩ := (exists_nonneg_word z).mpr hzy.2.1
    exact ⟨(word_map_val_lt v u).mp hlt, t', z', (fold_at_letters u t' v).mp htv,
      (tail_at_letters d hd t' x z').mp ht, (fold_at_letters u z' y).mp hzy⟩
  · rintro ⟨h, t, z, htv, ht, hzy⟩
    refine ⟨(word_map_val_lt v u).mpr h, List.map Subtype.val t, ?_,
      List.map Subtype.val z, ?_, (fold_at_letters ..).mpr htv, (tail_at_letters d hd ..).mpr ht,
      (fold_at_letters ..).mpr hzy⟩
    · simpa only [List.length_map, ← htv] using length_le_through shiftLetter u t
    · simpa only [List.length_map, ← hzy] using length_le_through shiftLetter u z

/-- The two bounded existential word quantifiers are eliminated in vector
coordinates using the actual shape bounds of the endpoints. -/
theorem def_rawIntervalGraph_of_tail (qe : HeadElimination V)
    (defTail : ∀ {k} (v x y : List (Term V k)),
      Definable {p | rawTailGraph d hd (evalWord v p) (evalWord x p) (evalWord y p)})
    {k} (v u x y : List (Term V k)) :
    Definable {p | rawIntervalGraph d hd (evalWord v p) (evalWord u p) (evalWord x p) (evalWord y p)} := by
  let Q (p : Fin k → V) (t z : List V) := rawFoldGraph (evalWord u p) t (evalWord v p) ∧
    rawTailGraph d hd t (evalWord x p) z ∧ rawFoldGraph (evalWord u p) z (evalWord y p)
  have defZ {m} (s : Fin k → Term V m) (t : List (Term V m)) :
      Definable {p | ∃ z : List V, z.length ≤ y.length ∧ Q (evalTuple s p) (evalWord t p) z} := by
    apply bounded_exists qe y.length
    intro l r z
    have h := (def_rawFoldGraph (u.map (·.subst s) |>.map (·.subst r)) (t.map (·.subst r))
          (v.map (·.subst s) |>.map (·.subst r))).inter
      ((defTail (t.map (·.subst r)) (x.map (·.subst s) |>.map (·.subst r)) z).inter
        (def_rawFoldGraph (u.map (·.subst s) |>.map (·.subst r)) z (y.map (·.subst s) |>.map (·.subst r))))
    convert h using 1
    ext p
    simp only [eval_subst_word, Q, mem_setOf_eq, mem_inter_iff]
  have h := (def_word_lt v u).inter
    (bounded_exists qe v.length (fun p t => ∃ z : List V, z.length ≤ y.length ∧ Q p t z) defZ)
  convert h using 1
  ext p
  simp only [rawIntervalGraph, evalWord, List.length_map, mem_setOf_eq, mem_inter_iff, Q]

/-- Unconditional semilinearity of interval coordinates under vector
quantifier elimination. -/
theorem def_rawIntervalGraph (qe : HeadElimination V) (d : Letter V)
    (hd : (⟨0, le_rfl⟩ : Letter V) < d) {k} (v u x y : List (Term V k)) :
    Definable {p | rawIntervalGraph d hd (evalWord v p) (evalWord u p) (evalWord x p) (evalWord y p)} :=
  def_rawIntervalGraph_of_tail d hd qe (def_rawTailGraph qe d hd) v u x y

end KnightModel.RankTwo.Semilinear
