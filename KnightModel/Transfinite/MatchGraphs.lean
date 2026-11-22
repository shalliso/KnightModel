import KnightModel.Transfinite.MatchWords
import KnightModel.RankTwo.ScottWordGraphs

/-! # First-order transfer of validity, proper image, and graph equality -/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}

/-- The same graph test may be used after an arbitrary finite extension of the index condition. -/
def GraphMatch (p : F.State)
    (r : WI I → WI I → Prop) (s : WI J → WI J → Prop) : Prop :=
  ∀ ⦃q : F.State⦄, q ≤ p → ∀ ⦃x y x' y'⦄,
    WordMatch q x x' → WordMatch q y y' → (r x y ↔ s x' y')

namespace GraphMatch
variable {p q : F.State} {r t : WI I → WI I → Prop} {s u : WI J → WI J → Prop}

theorem keep (h : GraphMatch p r s) (e : q ≤ p) : GraphMatch q r s :=
  fun _ f => h (f.trans e)

theorem symm (h : GraphMatch p r s) : GraphMatch p.symm s r := by
  intro q qp x y x' y' xx yy
  exact (h (OrderedBF.State.reverse_refines qp) xx.symm yy.symm).symm

/-- Only evaluation of the primitive graphs and word moves enter this system. -/
def system (h : GraphMatch p r s) (k : GraphMatch p t u) :
    BackAndForth (graphModel r t) (graphModel s u) where
  matchTuples a b := ∃ q : F.State, q ≤ p ∧ ∀ i, WordMatch q (a i) (b i)
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

theorem transfer (h : GraphMatch p r s) (k : GraphMatch p t u)
    (f : Formula GraphTest 0) :
    BackAndForth.Satisfies (graphModel r t) f ↔ BackAndForth.Satisfies (graphModel s u) f :=
  (h.system k).sentence_iff ⟨p,le_rfl,fun i => i.elim0⟩ f

theorem fullInitial (h : GraphMatch p r s) :
    (∃ e : WI I ↪o WI I, CoordinateFamily.FullInitial e ∧ ∀ x y, r x y ↔ e x = y) ↔
      ∃ e : WI J ↪o WI J, CoordinateFamily.FullInitial e ∧ ∀ x y, s x y ↔ e x = y :=
  (validGraph_iff r r).symm.trans ((h.transfer h _).trans (validGraph_iff s s))

theorem proper (h : GraphMatch p r s) :
    (∃ z, ∀ x, ¬ r x z) ↔ ∃ z, ∀ x, ¬ s x z :=
  (properGraph_iff r r).symm.trans ((h.transfer h _).trans (properGraph_iff s s))

theorem same (h : GraphMatch p r s) (k : GraphMatch p t u) :
    (∀ x y, r x y ↔ t x y) ↔ ∀ x y, s x y ↔ u x y :=
  (sameGraph_iff r t).symm.trans ((h.transfer k _).trans (sameGraph_iff s u))

end GraphMatch
end KnightModel.Transfinite
