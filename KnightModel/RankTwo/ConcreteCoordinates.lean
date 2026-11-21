import KnightModel.RankTwo.ConcreteModel
import KnightModel.RankTwo.ScottSchemes
import KnightModel.RankTwo.ScottBaseMatches

/-! # Back-and-forth moves on the concrete coordinate programs

A coordinate match identifies the two graphs under every extension of the
finite Knight correspondence. A scheme and its parameter word furnish the
witness for a new coordinate move. Graph validity transfers using the word
back-and-forth, so the target graph actually describes a full initial chart.
-/

namespace KnightModel.RankTwo.Concrete

open Scott

variable {Ω I J : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]
    [Nonempty I] [Nonempty J] {i : I} {j : J}

abbrev CodeMatch (p : ModelIsoCondition I J Ω) (c : Code i) (d : Code j) : Prop :=
  GraphMatch p (fun x y => c.val x = y) (fun x y => d.val x = y)

private theorem matchPresented {p : ModelIsoCondition I J Ω} {c : Code i} {d : Code j}
    {k : WordScheme} {u : WI I} {v : WI J}
    (m : GraphMatch p (schemeGraph i k u) (schemeGraph j k v))
    (hc : ∀ x y, schemeGraph i k u x y ↔ c.val x = y)
    (hd : ∀ x y, schemeGraph j k v x y ↔ d.val x = y) : CodeMatch p c d :=
  fun _ h _ _ _ _ xx yy => (hc _ _).symm.trans ((m h xx yy).trans (hd _ _))

theorem codeForth (localMatch : IntervalMatches (Ω := Ω) i j) {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) (c : Code i) :
    ∃ (q : ModelIsoCondition I J Ω) (d : Code j), q ≤ p ∧ CodeMatch q c d := by
  obtain ⟨k,u,hu,hc⟩ := c.property.1
  obtain ⟨q,v,qp,uv⟩ := WordMatch.forth p u
  have gm := schemeGraph_match localMatch (qp mark) k uv
  obtain ⟨e, hi, hg⟩ := gm.fullInitial.mp ⟨c.val, c.property.2, hc⟩
  let d : Code j := ⟨e, ⟨k, v, uv.length_eq.symm.trans hu, hg⟩, hi⟩
  exact ⟨q, d, qp, matchPresented gm hc hg⟩

theorem codeBack (localMatch : IntervalMatches (Ω := Ω) i j) {p : ModelIsoCondition I J Ω}
    (mark : (i,j) ∈ p.graph) (d : Code j) :
    ∃ (q : ModelIsoCondition I J Ω) (c : Code i), q ≤ p ∧ CodeMatch q c d := by
  obtain ⟨k,v,hv,hd⟩ := d.property.1
  obtain ⟨q,u,qp,uv⟩ := WordMatch.back p v
  have gm := schemeGraph_match localMatch (qp mark) k uv
  obtain ⟨e, hi, hg⟩ := gm.fullInitial.mpr ⟨d.val, d.property.2, hd⟩
  let c : Code i := ⟨e, ⟨k, u, uv.length_eq.trans hv, hg⟩, hi⟩
  exact ⟨q, c, qp, matchPresented gm hg hd⟩

theorem graphEq {a b : Code i} :
    (∀ x y, (a.val x = y ↔ b.val x = y)) ↔ a = b := by
  constructor
  · intro h
    exact Subtype.ext (DFunLike.ext _ _ fun x => ((h x _).mp rfl).symm)
  · rintro rfl; exact fun _ _ => Iff.rfl

private theorem compMatch {p : ModelIsoCondition I J Ω} {c e : Code i} {d f : Code j}
    (h : CodeMatch p c d) (k : CodeMatch p e f) :
    CodeMatch p ((family i).comp c e) ((family j).comp d f) := by
  intro q qp x y z w xx yy
  have m := (k.seq h) qp xx yy
  change (c.val (e.val x) = y ↔ d.val (f.val z) = w)
  simpa only [exists_eq_left'] using m

/-- The large and small frame actions use the same state, with finite index
extensions for base points, vectors, and coordinate schemes. -/
noncomputable def frameMatches (localMatch : IntervalMatches (Ω := Ω) i j)
    (S : SquareLadders OuterIndex (Cardinal.aleph 1).ord) (unc : ¬Countable J) :
    CoordinateMatches (BasePoints I) (BasePoints J) (smallAction i)
      (largeAction (Ω := Ω) S unc j) where
  State := {p : ModelIsoCondition I J Ω // (i,j) ∈ p.graph}
  param p := BaseMatch p.val
  code p := CodeMatch p.val
  one _ := fun _ _ _ _ _ _ xx yy => xx.eq_iff yy
  comp h k := compMatch h k
  proper {p c d} h := (proper_iff_gap c).trans ((GraphMatch.proper h).trans (proper_iff_gap d).symm)
  refines p q := q.val ≤ p.val
  keepParam h _ _ m := BaseMatch.keep m h
  keepCode h _ _ m := GraphMatch.keep m h
  paramForth p a := by
    obtain ⟨q, b, e, m⟩ := BaseMatch.forth p.val a
    exact ⟨⟨q,e p.property⟩, b, e, m⟩
  paramBack p b := by
    obtain ⟨q, a, e, m⟩ := BaseMatch.back p.val b
    exact ⟨⟨q,e p.property⟩, a, e, m⟩
  codeForth p c := by
    obtain ⟨q, d, e, m⟩ := codeForth localMatch p.property c
    exact ⟨⟨q,e p.property⟩, d, e, m⟩
  codeBack p d := by
    obtain ⟨q, c, e, m⟩ := codeBack localMatch p.property d
    exact ⟨⟨q,e p.property⟩, c, e, m⟩

end KnightModel.RankTwo.Concrete
