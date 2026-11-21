import KnightModel.RankTwo.WordFoldFormula
import KnightModel.RankTwo.WordBounds

/-! # Semilinearity of complementary-tail graphs -/

namespace KnightModel.RankTwo.Semilinear

open Word Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- Both the endpoint parameter word and the input/output words must lie in the alphabet. -/
def rawTailGraph (d : Letter V) (hd : (⟨0,le_rfl⟩ : Letter V) < d) (v x y : List V) : Prop :=
  ∃ t : List (Letter V), t.map Subtype.val = v ∧
    liftWordGraph Subtype.val (Word.TailGraph Word.shiftLetter ⟨0,le_rfl⟩ d hd Word.shiftOpenLetter t) x y

private abbrev valL : Letter V → V := Subtype.val

variable (d : Letter V) (hd : (⟨0,le_rfl⟩ : Letter V) < d)

omit [Module ℚ V] in
theorem rawTailGraph_map (v : List (Letter V)) (x y : List V) :
    rawTailGraph d hd (v.map valL) x y ↔
      liftWordGraph valL (TailGraph shiftLetter ⟨0,le_rfl⟩ d hd shiftOpenLetter v) x y := by
  constructor
  · rintro ⟨t,ht,h⟩
    obtain rfl : t = v := List.map_injective_iff.mpr Subtype.val_injective ht
    exact h
  · exact fun h => ⟨v,rfl,h⟩

private theorem rawFoldGraph_map_param (v : List (Letter V)) (x y : List V) :
    rawFoldGraph (v.map valL) x y ↔
      liftWordGraph valL (fun t z : List (Letter V) => through shiftLetter v t = z) x y := by
  rw [rawFoldGraph_iff]
  constructor
  · rintro ⟨t,ht,h⟩
    obtain rfl : t = v := List.map_injective_iff.mpr Subtype.val_injective ht
    exact h
  · exact fun h => ⟨v,rfl,h⟩

omit [Module ℚ V] in
private theorem rawSingleGraph_map_param (a : Letter V) (x y : List V) :
    rawSingleGraph a.val x y ↔ liftWordGraph valL
      (SingleGraph (⟨0,le_rfl⟩ : Letter V) shiftOpenLetter a) x y :=
  ⟨fun ⟨_,h⟩ => h, fun h => ⟨a.property,h⟩⟩

omit [Module ℚ V] in
theorem rawTailGraph_nil (x y : List V) : ¬ rawTailGraph d hd [] x y := by
  rintro ⟨t,ht,_,_,_,_,hn,_,_,_⟩
  exact hn (List.map_eq_nil_iff.mp ht)

omit [Module ℚ V] in
theorem rawTailGraph_one (a : V) (x y : List V) :
    rawTailGraph d hd [a] x y ↔ rawSingleGraph a x y := by
  by_cases ha : 0 ≤ a
  · let t : Letter V := ⟨a,ha⟩
    change rawTailGraph d hd ([t].map valL) x y ↔ rawSingleGraph t.val x y
    rw [rawTailGraph_map,rawSingleGraph_map_param]
    unfold liftWordGraph
    simp only [show ∀ x y : List (Letter V), TailGraph shiftLetter ⟨0,le_rfl⟩ d hd shiftOpenLetter [t] x y ↔
      SingleGraph ⟨0,le_rfl⟩ shiftOpenLetter t x y from tailGraph_singleton shiftLetter _ d hd shiftOpenLetter t]
  · constructor
    · rintro ⟨t,ht,_⟩
      exact (ha ((exists_nonneg_word [a]).mp ⟨t,ht⟩ a List.mem_cons_self)).elim
    · rintro ⟨hn,_⟩
      exact (ha hn).elim

set_option maxHeartbeats 1200000 in
/-- The two branch witnesses are respectively a single-fold preimage and
a single-translation preimage. The folded preimage never grows in length. -/
theorem rawTailGraph_cons (a b : V) (w x y : List V) :
    rawTailGraph d hd (a::b::w) x y ↔ (∀ t ∈ a::b::w, 0 ≤ t) ∧
      ((∃ t z : List V, rawFoldGraph [d.val] t x ∧
          rawTailGraph d hd (b::w) t z ∧ a::z = y) ∨
       (∃ t : List V, rawSingleGraph d.val t x ∧ rawSingleGraph a t y)) := by
  by_cases hv : ∀ t ∈ a::b::w, 0 ≤ t
  · rw [and_iff_right hv]
    obtain ⟨pars,hp⟩ := (exists_nonneg_word _).mpr hv
    cases pars with
    | nil => contradiction
    | cons aa pars =>
      cases pars with
      | nil => simp at hp
      | cons bb ws =>
        obtain ⟨rfl,rfl,rfl⟩ := (show aa.val = a ∧ bb.val = b ∧ ws.map valL = w by simpa using hp)
        change rawTailGraph d hd ((aa :: bb :: ws).map valL) x y ↔ _
        rw [rawTailGraph_map]
        have hj := List.map_injective_iff.mpr (@Subtype.val_injective V (· ∈ Ici 0))
        constructor
        · rintro ⟨X,Y,rfl,rfl,h⟩
          rcases (tailGraph_cons (A := Letter V) (shiftLetter (V := V)) (⟨0,le_rfl⟩ : Letter V) d hd (shiftOpenLetter (V := V)) aa bb ws X Y).mp h with
            ⟨t,z,hf,hc,hy⟩ | ⟨t,hl,hr⟩
          · exact .inl ⟨List.map valL t,List.map valL z,
              (rawFoldGraph_map_param [d] _ _).mpr ⟨t,X,rfl,rfl,hf⟩,
              (rawTailGraph_map d hd (bb::ws) _ _).mpr ⟨t,z,rfl,rfl,hc⟩,congrArg (List.map valL) hy⟩
          · exact .inr ⟨List.map valL t,(rawSingleGraph_map_param d _ _).mpr ⟨t,X,rfl,rfl,hl⟩,
              (rawSingleGraph_map_param aa _ _).mpr ⟨t,Y,rfl,rfl,hr⟩⟩
        · rintro (⟨t,z,hf,hc,rfl⟩ | ⟨t,hl,hr⟩)
          · obtain ⟨T,X,hT,rfl,hfold⟩ := (rawFoldGraph_map_param [d] _ _).mp hf
            obtain ⟨T',Z,hT',rfl,hchild⟩ := (rawTailGraph_map d hd (bb::ws) _ _).mp hc
            obtain rfl : T = T' := hj (hT.trans hT'.symm)
            exact ⟨X,aa::Z,rfl,rfl,(tailGraph_cons (A := Letter V) (shiftLetter (V := V)) (⟨0,le_rfl⟩ : Letter V) d hd (shiftOpenLetter (V := V)) aa bb ws X _).mpr
              (.inl ⟨T,Z,hfold,hchild,rfl⟩)⟩
          · obtain ⟨T,X,hT,rfl,hleft⟩ := (rawSingleGraph_map_param d _ _).mp hl
            obtain ⟨T',Y,hT',rfl,hright⟩ := (rawSingleGraph_map_param aa _ _).mp hr
            obtain rfl : T = T' := hj (hT.trans hT'.symm)
            exact ⟨X,Y,rfl,rfl,(tailGraph_cons (A := Letter V) (shiftLetter (V := V)) (⟨0,le_rfl⟩ : Letter V) d hd (shiftOpenLetter (V := V)) aa bb ws X Y).mpr
              (.inr ⟨T,hleft,hright⟩)⟩
  · constructor
    · rintro ⟨t,ht,_⟩
      exact (hv ((exists_nonneg_word _).mp ⟨t,ht⟩)).elim
    · rintro ⟨hn,_⟩
      exact (hv hn).elim


private theorem fold_preimage_length (u t x : List V) (h : rawFoldGraph u t x) :
    t.length ≤ x.length := by
  obtain ⟨e,_,T,X,rfl,rfl,he⟩ := (rawFoldGraph_iff u t x).mp h
  subst X
  simpa using (length_le_through shiftLetter e T)

omit [Module ℚ V] in
private theorem single_preimage_length (a : Letter V) (t x : List V) (h : rawSingleGraph a.val t x) :
    t.length ≤ x.length + 1 := by
  obtain ⟨T,X,rfl,rfl,hh⟩ := (rawSingleGraph_map_param a _ _).mp h
  simpa using ((prefixBounds_single (⟨0,le_rfl⟩ : Letter V) shiftOpenLetter a).sizes hh).1

/-- Bound a word witness before interpreting it as a tuple of scalar quantifiers. -/
omit [IsOrderedAddMonoid V] in
private theorem def_word_exists (qe : HeadElimination V) {k}
    (Q : (Fin k → V) → List V → Prop) (b : Nat)
    (symbolic : ∀ {m} (s : Fin k → Term V m) (w : List (Term V m)),
      Definable {p | Q (evalTuple s p) (evalWord w p)})
    (size : ∀ p w, Q p w → w.length ≤ b) : Definable {p | ∃ w, Q p w} := by
  convert bounded_exists qe b Q symbolic using 1
  ext p
  exact ⟨fun ⟨w,h⟩ => ⟨w,size p w h,h⟩,fun ⟨w,_,h⟩ => ⟨w,h⟩⟩

private theorem def_tail_subst (qe : HeadElimination V) {n}
    (v : List (Term V n)) : ∀ {k} (s : Fin n → Term V k) (x y : List (Term V k)),
      Definable {p | rawTailGraph d hd (evalWord v (evalTuple s p)) (evalWord x p) (evalWord y p)} := by
  induction v with
  | nil =>
    intro k s x y
    convert def_word_false (k := k) (V := V) using 1
    ext p
    exact ⟨rawTailGraph_nil d hd _ _,False.elim⟩
  | cons a v ih =>
    intro k s x y
    cases v with
    | nil =>
      convert def_word_single (a.subst s) x y using 1
      ext p
      simp only [Set.mem_setOf_eq,Term.eval_subst]
      exact rawTailGraph_one d hd _ _ _
    | cons b w =>
      let av := a.subst s
      let ep := (b::w).map (·.subst s)
      have valid := def_word_nonneg (av :: ep)
      let Right (p : Fin k → V) (t : List V) := rawSingleGraph d.val t (evalWord x p) ∧
        rawSingleGraph (av.eval p) t (evalWord y p)
      have hr : Definable {p | ∃ t, Right p t} := by
        apply def_word_exists qe Right (x.length + 1)
        · intro m r t
          have f := def_word_single (.const d.val) t (x.map (·.subst r))
          have g := def_word_single (av.subst r) t (y.map (·.subst r))
          convert f.inter g using 1
          ext p
          simp only [Right,Set.mem_setOf_eq,Set.mem_inter_iff,Term.eval,eval_subst_word,Term.eval_subst]
          rfl
        · intro p t h
          simpa only [evalWord,List.length_map] using single_preimage_length d t _ h.1
      let Left (z : List (Term V k)) (p : Fin k → V) (t : List V) :=
        rawFoldGraph [d.val] t (evalWord x p) ∧
          rawTailGraph d hd (evalWord ep p) t (evalWord z p)
      have hl (z : List (Term V k)) : Definable {p | ∃ t, Left z p t} := by
        apply def_word_exists qe (Left z) x.length
        · intro m r t
          have f := def_rawFoldGraph [.const d.val] t (x.map (·.subst r))
          have g := ih (fun i => (s i).subst r) t (z.map (·.subst r))
          convert f.inter g using 1
          ext p
          simp only [Left,ep,Set.mem_setOf_eq,Set.mem_inter_iff,eval_subst_word,eval_subst_tuple]
          rfl
        · intro p t h
          simpa only [evalWord,List.length_map] using fold_preimage_length _ _ _ h.1
      cases y with
      | nil =>
        convert valid.inter hr using 1
        ext p
        change rawTailGraph d hd (a.eval (evalTuple s p) :: b.eval (evalTuple s p) :: _)
          _ [] ↔ _
        rw [rawTailGraph_cons]
        have e : evalWord ep p = evalWord (b::w) (evalTuple s p) := eval_subst_word _ _ _
        have e' : av.eval p = a.eval (evalTuple s p) := Term.eval_subst _ _ _
        change (_ ∧ (_ ∨ _)) ↔ (∀ q ∈ av.eval p :: evalWord ep p, 0 ≤ q) ∧
          ∃ t, rawSingleGraph d.val t _ ∧ rawSingleGraph (av.eval p) t []
        rw [e,e']
        apply and_congr Iff.rfl
        exact ⟨fun h => h.elim (fun ⟨_,_,_,_,e⟩ => List.cons_ne_nil _ _ e |>.elim) id, Or.inr⟩
      | cons c z =>
        convert valid.inter (((def_term_eq av c).inter (hl z)).union hr) using 1
        ext p
        change rawTailGraph d hd (a.eval (evalTuple s p) :: b.eval (evalTuple s p) :: _)
          _ (c.eval p :: evalWord z p) ↔ _
        rw [rawTailGraph_cons]
        have e : evalWord ep p = evalWord (b::w) (evalTuple s p) := eval_subst_word _ _ _
        have e' : av.eval p = a.eval (evalTuple s p) := Term.eval_subst _ _ _
        change (_ ∧ (_ ∨ _)) ↔ (∀ q ∈ av.eval p :: evalWord ep p, 0 ≤ q) ∧
          ((av.eval p = c.eval p ∧ ∃ t, rawFoldGraph [d.val] t _ ∧ rawTailGraph d hd (evalWord ep p) t _) ∨
           ∃ t, rawSingleGraph d.val t _ ∧ rawSingleGraph (av.eval p) t _)
        rw [e,e']
        apply and_congr Iff.rfl (or_congr _ Iff.rfl)
        constructor
        · rintro ⟨t,Z,ht,hY,h⟩
          exact ⟨(List.cons.inj h).1,t,ht,(List.cons.inj h).2 ▸ hY⟩
        · rintro ⟨h,t,ht,hY⟩
          exact ⟨t,_,ht,hY,congrArg (· :: evalWord z p) h⟩

/-- Every fixed-shape positive-letter tail chart has a semilinear graph in all
of its endpoint, input, and output coordinates. -/
theorem def_rawTailGraph (qe : HeadElimination V) (d : Letter V)
    (hd : (⟨0,le_rfl⟩ : Letter V) < d) {k} (v x y : List (Term V k)) :
    Definable {p | rawTailGraph d hd (evalWord v p) (evalWord x p) (evalWord y p)} :=
  def_tail_subst d hd qe v (Term.var ·) x y

end KnightModel.RankTwo.Semilinear
