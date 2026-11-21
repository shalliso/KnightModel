import KnightModel.RankTwo.ScottWords
import KnightModel.RankTwo.AtlasCoordinates

/-! # Detecting total initial coordinates by first-order graph tests -/

namespace KnightModel.RankTwo.Scott

inductive GraphTest : Nat → Type where
  | lt : GraphTest 2
  | first : GraphTest 2
  | second : GraphTest 2

variable {W : Type} [LinearOrder W]

def graphModel (r s : W → W → Prop) : Model GraphTest W
  | _, .lt, a => a 0 < a 1
  | _, .first, a => r (a 0) (a 1)
  | _, .second, a => s (a 0) (a 1)

private def test {n : Nat} (r : GraphTest 2) (a b : Fin n) : Formula GraphTest n :=
  .atom (.rel r (Fin.cases a (fun _ => b)))

private def total : Formula GraphTest 0 := .all (.ex (test .first 1 0))
private def functional : Formula GraphTest 0 :=
  .all (.all (.all (((test .first 2 1).and (test .first 2 0)).implies (.atom (.eq 1 0)))))
private def increasing : Formula GraphTest 0 :=
  .all (.all (.all (.all ((((test .first 3 2).and (test .first 1 0)).and (test .lt 3 1)).implies
    (test .lt 2 0)))))
private def downward : Formula GraphTest 0 :=
  .all (.all (.all (((test .first 2 1).and (test .lt 0 1)).implies (.ex (test .first 0 1)))))

def validGraphSentence : Formula GraphTest 0 := (total.and functional).and (increasing.and downward)
def properGraphSentence : Formula GraphTest 0 := .ex (.all (.neg (test .first 0 1)))
def sameGraphSentence : Formula GraphTest 0 := .all (.all (
  ((test .first 1 0).implies (test .second 1 0)).and ((test .second 1 0).implies (test .first 1 0))))

theorem properGraph_iff (r s : W → W → Prop) :
    BackAndForth.Satisfies (graphModel r s) properGraphSentence ↔ ∃ z, ∀ x, ¬ r x z := by
  change (∃ z, (Formula.all _).Holds _ _) ↔ _
  simp only [Formula.holds_all]
  rfl

theorem sameGraph_iff (r s : W → W → Prop) :
    BackAndForth.Satisfies (graphModel r s) sameGraphSentence ↔ ∀ x y, r x y ↔ s x y := by
  simp only [BackAndForth.Satisfies, sameGraphSentence, Formula.holds_all, Formula.holds_and, Formula.holds_implies]
  change (∀ x y, (r x y → s x y) ∧ (s x y → r x y)) ↔ _
  exact forall_congr' (fun x => forall_congr' (fun y => iff_def.symm))

theorem validGraph_iff [OrderTop W] (r s : W → W → Prop) :
    BackAndForth.Satisfies (graphModel r s) validGraphSentence ↔
      ∃ e : W ↪o W, CoordinateFamily.FullInitial e ∧ ∀ x y, r x y ↔ e x = y := by
  simp only [BackAndForth.Satisfies, validGraphSentence, total, functional, increasing, downward,
    Formula.holds_and, Formula.holds_all, Formula.holds_implies]
  change (((∀ x, ∃ y, r x y) ∧ (∀ x y z, r x y ∧ r x z → y = z)) ∧
    ((∀ x y z w, (r x y ∧ r z w) ∧ x < z → y < w) ∧
      (∀ x y z, r x y ∧ z < y → ∃ w, r w z))) ↔ _
  constructor
  · rintro ⟨⟨tot, unique⟩, mono, down⟩
    let f := fun x => (tot x).choose
    have spec x : r x (f x) := (tot x).choose_spec
    let e : W ↪o W := OrderEmbedding.ofStrictMono f (fun x z h =>
      mono x _ z _ ⟨⟨spec x, spec z⟩, h⟩)
    have graph x y : r x y ↔ e x = y :=
      ⟨fun h => unique x _ _ ⟨spec x, h⟩, fun h => h ▸ spec x⟩
    refine ⟨e, ?_, graph⟩
    ext y
    constructor
    · rintro ⟨x,rfl⟩; exact e.monotone le_top
    · intro h
      obtain hy | hy := lt_or_eq_of_le h
      · obtain ⟨z, hz⟩ := down ⊤ _ y ⟨spec ⊤, hy⟩
        exact ⟨z, (graph z y).mp hz⟩
      · exact ⟨⊤, hy.symm⟩
  · rintro ⟨e, he, hr⟩
    simp_rw [hr]
    refine ⟨⟨fun x => ⟨e x, rfl⟩, ?_⟩, ?_, ?_⟩
    · rintro x _ _ ⟨rfl, rfl⟩; rfl
    · rintro x _ z _ ⟨⟨rfl, rfl⟩, h⟩; exact e.strictMono h
    · rintro x _ z ⟨rfl, h⟩
      have hz : z ∈ Set.Iic (e ⊤) := h.le.trans (e.monotone le_top)
      change z ∈ Set.range e
      rwa [he]

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]

abbrev WI (I : Type) [LinearOrder I] := Word (Letter I)

/-- The same graph test may be used after an arbitrary finite extension of the index condition. -/
def GraphMatch (p : ModelIsoCondition I J Ω)
    (r : WI I → WI I → Prop) (s : WI J → WI J → Prop) : Prop :=
  ∀ ⦃q : ModelIsoCondition I J Ω⦄, q ≤ p → ∀ ⦃x y x' y'⦄,
    WordMatch q x x' → WordMatch q y y' → (r x y ↔ s x' y')

namespace GraphMatch
variable {p q : ModelIsoCondition I J Ω} {r t : WI I → WI I → Prop} {s u : WI J → WI J → Prop}

theorem keep (h : GraphMatch p r s) (e : q ≤ p) : GraphMatch q r s :=
  fun _ f => h (f.trans e)

/-- Only evaluation of the primitive graphs and word moves enter this system. -/
def system [Nonempty I] [Nonempty J] (h : GraphMatch p r s) (k : GraphMatch p t u) :
    BackAndForth (graphModel r t) (graphModel s u) where
  matchTuples a b := ∃ q : ModelIsoCondition I J Ω, q ≤ p ∧ ∀ i, WordMatch q (a i) (b i)
  atoms := by
    rintro n a b ⟨q, qp, m⟩ v
    cases v with
    | eq i j => exact (m i).eq_iff (m j)
    | rel c f =>
      cases c with
      | lt => exact (m (f 0)).lt_iff (m (f 1))
      | first => exact h qp (m (f 0)) (m (f 1))
      | second => exact k qp (m (f 0)) (m (f 1))
  forth := by
    rintro n a b ⟨q, qp, m⟩ x
    obtain ⟨v,y,vq,xy⟩ := WordMatch.forth q x
    exact ⟨y,v,vq.trans qp,Fin.cases xy (fun i => (m i).keep vq)⟩
  back := by
    rintro n a b ⟨q, qp, m⟩ y
    obtain ⟨v,x,vq,xy⟩ := WordMatch.back q y
    exact ⟨x,v,vq.trans qp,Fin.cases xy (fun i => (m i).keep vq)⟩

theorem transfer [Nonempty I] [Nonempty J] (h : GraphMatch p r s) (k : GraphMatch p t u)
    (f : Formula GraphTest 0) :
    BackAndForth.Satisfies (graphModel r t) f ↔ BackAndForth.Satisfies (graphModel s u) f :=
  (h.system k).sentence_iff ⟨p,le_rfl,fun i => i.elim0⟩ f

theorem fullInitial [Nonempty I] [Nonempty J] (h : GraphMatch p r s) :
    (∃ e : WI I ↪o WI I, CoordinateFamily.FullInitial e ∧ ∀ x y, r x y ↔ e x = y) ↔
      ∃ e : WI J ↪o WI J, CoordinateFamily.FullInitial e ∧ ∀ x y, s x y ↔ e x = y :=
  (validGraph_iff r r).symm.trans ((h.transfer h _).trans (validGraph_iff s s))

theorem proper [Nonempty I] [Nonempty J] (h : GraphMatch p r s) :
    (∃ z, ∀ x, ¬ r x z) ↔ ∃ z, ∀ x, ¬ s x z :=
  (properGraph_iff r r).symm.trans ((h.transfer h _).trans (properGraph_iff s s))

theorem same [Nonempty I] [Nonempty J] (h : GraphMatch p r s) (k : GraphMatch p t u) :
    (∀ x y, r x y ↔ t x y) ↔ ∀ x y, s x y ↔ u x y :=
  (sameGraph_iff r t).symm.trans ((h.transfer k _).trans (sameGraph_iff s u))

end GraphMatch
end KnightModel.RankTwo.Scott
