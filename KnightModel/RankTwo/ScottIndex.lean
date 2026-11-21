import KnightModel.RankTwo.ScottSentence
import KnightModel.Model.Condition

/-! # Pointed Knight models as a back-and-forth system

The graph of each named Knight function is a binary relation. Marking an index is
a unary relation. The repository's finite partial Knight isomorphisms give matches
even when one of the models is uncountable.
-/

namespace KnightModel.RankTwo.Scott

inductive IndexRelation (Ω : Type) : Nat → Type where
  | order : IndexRelation Ω 2
  | graph (c : Ω) : IndexRelation Ω 2
  | mark : IndexRelation Ω 1

variable {Ω I J : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]

def indexModel (i : I) : Model (IndexRelation Ω) I
  | _, .order, t => t 0 ≤ t 1
  | _, .graph c, t => t 1 = KnightModel.fn c (t 0)
  | _, .mark, t => t 0 = i

private theorem addLeft [Nonempty J] (p : ModelIsoCondition I J Ω) (a : I) :
    ∃ (q : ModelIsoCondition I J Ω) b, q ≤ p ∧ (a,b) ∈ q.graph := by
  by_cases h : a ∈ p.dom
  · obtain ⟨b, hb⟩ := p.mem_dom_iff.mp h
    exact ⟨p, b, le_rfl, hb⟩
  · obtain ⟨b, hb⟩ := p.canExtend_domain a h
    obtain ⟨q, hq, hmem⟩ := hb.exists_extension
    exact ⟨q, b, hq, hmem⟩

private theorem addRight [Nonempty I] (p : ModelIsoCondition I J Ω) (b : J) :
    ∃ (q : ModelIsoCondition I J Ω) a, q ≤ p ∧ (a,b) ∈ q.graph := by
  by_cases h : b ∈ p.ran
  · obtain ⟨a, ha⟩ := p.mem_ran_iff.mp h
    exact ⟨p, a, le_rfl, ha⟩
  · obtain ⟨a, ha⟩ := p.canExtend_range b h
    obtain ⟨q, hq, hmem⟩ := ha.exists_extension
    exact ⟨q, a, hq, hmem⟩

private theorem pair_eq (p : ModelIsoCondition I J Ω) {a b c d}
    (h : (a,b) ∈ p.graph) (k : (c,d) ∈ p.graph) : a = c ↔ b = d :=
  ⟨p.functional _ h _ k, p.injective _ h _ k⟩

def indexSystem [Nonempty I] [Nonempty J] (i : I) (j : J) :
    BackAndForth (indexModel (Ω := Ω) i) (indexModel (Ω := Ω) j) where
  matchTuples := fun s t => ∃ p : ModelIsoCondition I J Ω,
    (i,j) ∈ p.graph ∧ ∀ l, (s l,t l) ∈ p.graph
  atoms := by
    rintro n s t ⟨p, mark, g⟩ r
    cases r with
    | eq k l => exact pair_eq p (g k) (g l)
    | rel v f =>
      cases v with
      | order => exact p.toPartialIso.order_pres_iff (g (f 0)) (g (f 1))
      | graph c => exact p.fn_compat c _ (g (f 0)) _ (g (f 1))
      | mark => exact pair_eq p (g (f 0)) mark
  forth := by
    rintro n s t ⟨p, mark, g⟩ a
    obtain ⟨q, b, e, h⟩ := addLeft p a
    exact ⟨b, q, e mark, Fin.cases h (fun l => e (g l))⟩
  back := by
    rintro n s t ⟨p, mark, g⟩ b
    obtain ⟨q, a, e, h⟩ := addRight p b
    exact ⟨a, q, e mark, Fin.cases h (fun l => e (g l))⟩

/-- Given a distinguished index in the first model, choose its matching index in the
second. The resulting pointed models satisfy precisely the same infinitary sentences. -/
theorem exists_matching_index [Nonempty I] [Nonempty J] (i : I) :
    ∃ j : J, ∀ p : Formula (IndexRelation Ω) 0,
      BackAndForth.Satisfies (indexModel i) p ↔ BackAndForth.Satisfies (indexModel j) p := by
  obtain ⟨q, j, _, h⟩ := addLeft (ModelIsoCondition.empty : ModelIsoCondition I J Ω) i
  exact ⟨j, fun p => (indexSystem (Ω := Ω) i j).sentence_iff ⟨q, h, fun l => l.elim0⟩ p⟩

end KnightModel.RankTwo.Scott
