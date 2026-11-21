import KnightModel.RankTwo.ScottWordGraphs
import KnightModel.RankTwo.AtlasKnight

/-! # Finite composition of transported word programs

The only interval primitives that remain to be analyzed locally are the
normalized open interval and the complementary tail. All Boolean and
composition operations follow from the back-and-forth over finite supports.
-/

namespace KnightModel.RankTwo.Scott

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]
variable [Nonempty I] [Nonempty J]

abbrev schemeGraph (i : I) (k : WordScheme) (s : WI I) :=
  k.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter s

namespace GraphMatch
variable {p : ModelIsoCondition I J Ω} {r t : WI I → WI I → Prop} {s u : WI J → WI J → Prop}

omit [Nonempty I] [Nonempty J] in
theorem congr (h : GraphMatch p r s) (left : ∀ x y, r x y ↔ t x y)
    (right : ∀ x y, s x y ↔ u x y) : GraphMatch p t u :=
  fun _ e _ _ _ _ xx yy => (left _ _).symm.trans ((h e xx yy).trans (right _ _))

omit [Nonempty I] [Nonempty J] in
theorem inv (h : GraphMatch p r s) :
    GraphMatch p (fun x y => r y x) (fun x y => s y x) :=
  fun _ e _ _ _ _ xx yy => h e yy xx

omit [Nonempty I] [Nonempty J] in
theorem union (h : GraphMatch p r s) (k : GraphMatch p t u) :
    GraphMatch p (fun x y => r x y ∨ t x y) (fun x y => s x y ∨ u x y) :=
  fun _ e _ _ _ _ xx yy => (h e xx yy).or (k e xx yy)

theorem seq (h : GraphMatch p r s) (k : GraphMatch p t u) :
    GraphMatch p (fun x y => ∃ z, r x z ∧ t z y) (fun x y => ∃ z, s x z ∧ u z y) := by
  intro q qp x y x' y' xx yy
  constructor
  · rintro ⟨z,hz,kz⟩
    obtain ⟨l,z',lq,zz⟩ := WordMatch.forth q z
    exact ⟨z', (h (lq.trans qp) (xx.keep lq) zz).mp hz, (k (lq.trans qp) zz (yy.keep lq)).mp kz⟩
  · rintro ⟨z',hz,kz⟩
    obtain ⟨l,z,lq,zz⟩ := WordMatch.back q z'
    exact ⟨z, (h (lq.trans qp) (xx.keep lq) zz).mpr hz, (k (lq.trans qp) zz (yy.keep lq)).mpr kz⟩

end GraphMatch

/-- The two concrete interval primitive tests to be verified for the distinguished letters. -/
structure IntervalMatches (i : I) (j : J) : Prop where
  tail : ∀ {p : ModelIsoCondition I J Ω}, (i,j) ∈ p.graph → ∀ (n : Nat) {s t}, WordMatch p s t →
    GraphMatch p (schemeGraph i (.tail n) s) (schemeGraph j (.tail n) t)
  interval : ∀ {p : ModelIsoCondition I J Ω}, (i,j) ∈ p.graph → ∀ (m n : Nat) {s t},
    WordMatch p s t →
    GraphMatch p (schemeGraph i (.interval m n) s) (schemeGraph j (.interval m n) t)

theorem schemeGraph_match {i : I} {j : J} (A : IntervalMatches (Ω := Ω) i j)
    {p : ModelIsoCondition I J Ω} (mark : (i,j) ∈ p.graph)
    (c : WordScheme) {s t} (h : WordMatch p s t) :
    GraphMatch p (schemeGraph i c s) (schemeGraph j c t) := by
  induction c generalizing s t with
  | id => exact fun _ _ _ _ _ _ xx yy => xx.eq_iff yy
  | empty => exact fun _ _ _ _ _ _ _ _ => Iff.rfl
  | «prefix» n => exact fun _ e _ _ _ _ xx yy => ((h.keep e).prepend xx).eq_iff yy
  | through n => exact fun _ e _ _ _ _ xx yy => ((h.keep e).through xx).eq_iff yy
  | interval m n => exact A.interval mark m n h
  | tail n => exact A.tail mark n h
  | atMost n => exact fun _ e _ _ _ _ xx yy => (xx.le_iff (h.keep e)).and (xx.eq_iff yy)
  | above n => exact fun _ e _ _ _ _ xx yy => ((h.keep e).lt_iff xx).and (xx.eq_iff yy)
  | seq f g ih jh => exact (ih (List.forall₂_take f.arity h)).seq (jh (List.forall₂_drop f.arity h))
  | union f g ih jh => exact fun _ e _ _ _ _ xx yy =>
      (ih (List.forall₂_take f.arity h) e xx yy).or (jh (List.forall₂_drop f.arity h) e xx yy)
  | inv f ih => exact fun _ e _ _ _ _ xx yy => ih h e yy xx

end KnightModel.RankTwo.Scott
