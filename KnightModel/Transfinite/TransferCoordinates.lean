import KnightModel.Transfinite.TransferRun
import KnightModel.Transfinite.SuccessorModel

/-! # Finite coordinate states for the actual successor frame actions -/

namespace KnightModel.Transfinite

open RankTwo Scott Concrete Cardinal

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}
variable {i : I} {j : J}

abbrev CodeMatch (p : F.State) (c : Code i) (d : Code j) : Prop :=
  GraphMatch p (fun x y => c.val x = y) (fun x y => d.val x = y)

private theorem matchPresented {p : F.State} {c : Code i} {d : Code j}
    {k : WordScheme} {u : WI I} {v : WI J}
    (m : GraphMatch p (schemeGraph i k u) (schemeGraph j k v))
    (hc : ∀ x y, schemeGraph i k u x y ↔ c.val x = y)
    (hd : ∀ x y, schemeGraph j k v x y ↔ d.val x = y) : CodeMatch p c d :=
  fun _ h _ _ _ _ xx yy => (hc _ _).symm.trans ((m h xx yy).trans (hd _ _))

theorem codeForth {p : F.State}
    (mark : (i,j) ∈ p.graph) (c : Code i) :
    ∃ (q : F.State) (d : Code j), q ≤ p ∧ CodeMatch q c d := by
  obtain ⟨k,u,hu,hc⟩ := c.property.1
  obtain ⟨q,v,qp,uv⟩ := WordMatch.forth p u
  have gm := orderedScheme_match (qp mark) k uv
  obtain ⟨e, hi, hg⟩ := gm.fullInitial.mp ⟨c.val, c.property.2, hc⟩
  let d : Code j := ⟨e, ⟨k, v, uv.length_eq.symm.trans hu, hg⟩, hi⟩
  exact ⟨q, d, qp, matchPresented gm hc hg⟩

theorem codeBack {p : F.State} (mark : (i,j) ∈ p.graph) (d : Code j) :
    ∃ (q : F.State) (c : Code i), q ≤ p ∧ CodeMatch q c d := by
  obtain ⟨q,c,qp,matchCode⟩ := codeForth (p := p.symm) (OrderedBF.State.mem_symm_graph.mpr mark) d
  exact ⟨q.symm,c,OrderedBF.State.reverse_refines qp,matchCode.symm⟩

private theorem compMatch {p : F.State} {c e : Code i} {d f : Code j}
    (h : CodeMatch p c d) (k : CodeMatch p e f) :
    CodeMatch p ((family i).comp c e) ((family j).comp d f) := by
  intro q qp x y z w xx yy
  have m := (k.seq h) qp xx yy
  change (c.val (e.val x) = y ↔ d.val (f.val z) = w)
  simpa only [exists_eq_left'] using m

/-- The large and small frame actions use the same state, with finite index
extensions for base points, vectors, and coordinate schemes. -/
noncomputable def frameMatches (F : OrderedBF D E) (i : I) (j : J)
    (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o J) :
    CoordinateMatches (BasePoints I) (BasePoints J) (smallAction i)
      (largeAction j κ hκ S slots) where
  State := {p : F.State // (i,j) ∈ p.graph}
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
    obtain ⟨q, d, e, m⟩ := codeForth p.property c
    exact ⟨⟨q,e p.property⟩, d, e, m⟩
  codeBack p d := by
    obtain ⟨q, c, e, m⟩ := codeBack p.property d
    exact ⟨⟨q,e p.property⟩, c, e, m⟩

end KnightModel.Transfinite
