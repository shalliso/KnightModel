import KnightModel.RankTwo.ScottSchemes
import KnightModel.RankTwo.WordEvaluation

/-! # Transporting the two interval primitives over finite Knight conditions -/

namespace KnightModel.RankTwo.Scott

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]
variable [Nonempty I] [Nonempty J]

private abbrev zeroLetter (I : Type) [LinearOrder I] : Letter I := ⟨0,le_rfl⟩
private abbrev singleR (a : Letter I) := Word.SingleGraph (zeroLetter I) Word.shiftOpenLetter a
private abbrev tailR (i : I) (v : WI I) :=
  Word.TailGraph Word.shiftLetter (zeroLetter I) (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter v
private abbrev normR (i : I) (v u : WI I) :=
  Word.HGraph Word.shiftLetter (zeroLetter I) (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter v u

omit [Nonempty I] [Nonempty J] in
private theorem single_match {p : ModelIsoCondition I J Ω} {a : Letter I} {b : Letter J}
    (ab : LetterMatch p a b) : GraphMatch p (singleR a) (singleR b) := by
  intro q qp x y x' y' xx yy
  cases xx with
  | nil =>
    exact (Word.singleGraph_root _ _ a y).trans ((yy.eq_iff .nil).trans (Word.singleGraph_root _ _ b y').symm)
  | @cons c d v w cd vw =>
    refine (Word.singleGraph_cons _ _ a c v y).trans (Iff.trans ?_ (Word.singleGraph_cons _ _ b d w y').symm)
    have pos : zeroLetter I < c ↔ zeroLetter J < d := VectorMatch.zero.lt_iff cd
    constructor
    · rintro ⟨h,e⟩
      refine ⟨pos.mp h, ?_⟩
      apply (yy.eq_iff (.cons (cd.add (ab.keep qp)) vw)).mp e
    · rintro ⟨h,e⟩
      refine ⟨pos.mpr h, ?_⟩
      apply (yy.eq_iff (.cons (cd.add (ab.keep qp)) vw)).mpr e

private theorem tail_match {i : I} {j : J} {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) {s t} (m : WordMatch p s t) :
    GraphMatch p (tailR i s) (tailR j t) := by
  induction m with
  | nil =>
    intro q qp x y x' y' xx yy
    exact iff_of_false (fun ⟨h,_⟩ => h rfl) (fun ⟨h,_⟩ => h rfl)
  | @cons a b s t ab st ih =>
    have addHead : GraphMatch p (fun x y => Word.cons a x = y) (fun x y => Word.cons b x = y) :=
      fun _ e _ _ _ _ xx yy => WordMatch.eq_iff (.cons (ab.keep e) xx) yy
    have dd : LetterMatch p (unitLetter i) (unitLetter j) := VectorMatch.single mark 1
    have fold : GraphMatch p (fun x y => Word.through Word.shiftLetter (Word.cons (unitLetter i) Word.root) x = y)
        (fun x y => Word.through Word.shiftLetter (Word.cons (unitLetter j) Word.root) x = y) :=
      fun _ e _ _ _ _ xx yy => WordMatch.eq_iff (WordMatch.through (.cons (dd.keep e) .nil) xx) yy
    cases st with
    | nil =>
      exact (single_match ab).congr
        (fun x y => (Word.tailGraph_singleton _ _ _ _ _ _ x y).symm)
        (fun x y => (Word.tailGraph_singleton _ _ _ _ _ _ x y).symm)
    | @cons c d w w' cd ww =>
      apply ((fold.inv.seq (ih.seq addHead)).union ((single_match dd).inv.seq (single_match ab))).congr
      · intro x y
        refine Iff.trans (or_congr ?_ Iff.rfl) (Word.tailGraph_cons _ _ _ _ _ _ _ _ x y).symm
        constructor
        · rintro ⟨t,h,z,k,l⟩; exact ⟨t,z,h,k,l⟩
        · rintro ⟨t,z,h,k,l⟩; exact ⟨t,h,z,k,l⟩
      · intro x y
        refine Iff.trans (or_congr ?_ Iff.rfl) (Word.tailGraph_cons _ _ _ _ _ _ _ _ x y).symm
        constructor
        · rintro ⟨t,h,z,k,l⟩; exact ⟨t,z,h,k,l⟩
        · rintro ⟨t,z,h,k,l⟩; exact ⟨t,h,z,k,l⟩

private abbrev rawR (i : I) (v u : WI I) (x y : WI I) :=
  ∃ (h : v < u) (z : Set.Ioi (Word.cons (zeroLetter I) Word.root)), x = z.val ∧
    y = (Word.intervalIso Word.shiftLetter (zeroLetter I) (unitLetter i) (zero_lt_unit i)
      Word.shiftOpenLetter h z).val

omit [Nonempty I] in
private theorem raw_form (i : I) (v u x y : WI I) : rawR i v u x y ↔
    v < u ∧ ∃ t z : WI I, Word.through Word.shiftLetter u t = v ∧
      tailR i t x z ∧ Word.through Word.shiftLetter u z = y := by
  constructor
  · rintro ⟨h,g⟩
    exact ⟨h, (Word.interval_graph _ _ _ _ _ v u h x y).mp g⟩
  · rintro ⟨h,g⟩
    exact ⟨h, (Word.interval_graph _ _ _ _ _ v u h x y).mpr g⟩

private theorem raw_forward {i : I} {j : J} {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) {v v' u u' x x' y y'} (vv : WordMatch p v v')
    (uu : WordMatch p u u') (xx : WordMatch p x x') (yy : WordMatch p y y')
    (h : rawR i v u x y) : rawR j v' u' x' y' := by
  obtain ⟨vu,t,z,ht,hg,hz⟩ := (raw_form _ _ _ _ _).mp h
  obtain ⟨q,t',qp,tt⟩ := WordMatch.forth p t
  obtain ⟨l,z',lq,zz⟩ := WordMatch.forth q z
  let lp := lq.trans qp
  refine (raw_form _ _ _ _ _).mpr ⟨(vv.lt_iff uu).mp vu,t',z',?_,?_,?_⟩
  · exact ((((uu.keep qp).through tt).eq_iff (vv.keep qp)).mp ht)
  · exact (tail_match (qp mark) tt lq (xx.keep lp) zz).mp hg
  · exact (((uu.keep lp).through zz).eq_iff (yy.keep lp)).mp hz

private theorem raw_match {i : I} {j : J} {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) {v v' u u'} (vv : WordMatch p v v') (uu : WordMatch p u u') :
    GraphMatch p (rawR i v u) (rawR j v' u') := by
  intro q qp x y x' y' xx yy
  exact ⟨raw_forward (qp mark) (vv.keep qp) (uu.keep qp) xx yy,
    raw_forward (ModelIsoCondition.mem_symm_graph.mpr (qp mark)) (vv.keep qp).symm (uu.keep qp).symm
      xx.symm yy.symm⟩

omit [Nonempty I] in
private theorem raw_norm (i : I) {v u : WI I} (e : ∀ h : v < u,
    Word.H Word.shiftLetter (zeroLetter I) (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter v u h =
    Word.intervalIso Word.shiftLetter (zeroLetter I) (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter h)
    (x y : WI I) : rawR i v u x y ↔ normR i v u x y := by
  exact exists_congr fun h => exists_congr fun z => and_congr_right fun _ => by rw [e h]

private theorem norm_match {i : I} {j : J} {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) {v v' u u'} (vv : WordMatch p v v') (uu : WordMatch p u u') :
    GraphMatch p (normR i v u) (normR j v' u') := by
  induction vv generalizing u u' with
  | nil =>
    intro q qp x y x' y' xx yy
    exact iff_of_false (fun ⟨h,_⟩ => (Word.le_root _).not_gt h) (fun ⟨h,_⟩ => (Word.le_root _).not_gt h)
  | @cons a b v v' ab vv ih =>
    cases uu with
    | nil =>
      exact (raw_match mark (.cons ab vv) .nil).congr
        (raw_norm _ (fun h => Word.H_at_root _ _ _ _ _ _ h))
        (raw_norm _ (fun h => Word.H_at_root _ _ _ _ _ _ h))
    | @cons c d u u' cd uu =>
      by_cases ac : a = c
      · have bd : b = d := Subtype.ext ((ab.eq_iff cd).mp (congrArg Subtype.val ac))
        subst c
        subst d
        have head : GraphMatch p (fun x y => Word.cons a x = y) (fun x y => Word.cons b x = y) :=
          fun _ e _ _ _ _ xx yy => WordMatch.eq_iff (.cons (ab.keep e) xx) yy
        exact ((ih uu).seq head).congr
          (fun x y => (Word.hgraph_common _ _ _ _ _ a v u x y).symm)
          (fun x y => (Word.hgraph_common _ _ _ _ _ b v' u' x y).symm)
      · have bd : b ≠ d := fun h => ac (Subtype.ext ((ab.eq_iff cd).mpr (congrArg Subtype.val h)))
        exact (raw_match mark (.cons ab vv) (.cons cd uu)).congr
          (raw_norm _ (fun h => Word.H_different _ _ _ _ _ a c v u h ac))
          (raw_norm _ (fun h => Word.H_different _ _ _ _ _ b d v' u' h bd))

/-- Every interval and tail program actually respects the finite Knight support matches. -/
theorem intervalMatches (i : I) (j : J) : IntervalMatches (Ω := Ω) i j where
  tail := by intro p mark n s t h; exact tail_match mark h
  interval := by intro p mark m n s t h; exact norm_match mark (List.forall₂_take m h) (List.forall₂_drop m h)

/-- Transport of every graph in the countable program language. -/
theorem knightScheme_match {i : I} {j : J} {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) (c : WordScheme) {s t} (h : WordMatch p s t) :
    GraphMatch p (schemeGraph i c s) (schemeGraph j c t) :=
  schemeGraph_match (intervalMatches i j) mark c h

end KnightModel.RankTwo.Scott
