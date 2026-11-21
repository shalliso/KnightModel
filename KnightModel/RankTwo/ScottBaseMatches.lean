import KnightModel.RankTwo.BaseLanguage
import KnightModel.RankTwo.ScottWords

/-! # Atomic diagrams on the actual index and vector sorts -/

namespace KnightModel.RankTwo.Scott

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]

def BaseMatch (p : ModelIsoCondition I J Ω) : BasePoints I → BasePoints J → Prop
  | .inl i, .inl j => (i,j) ∈ p.graph
  | .inr v, .inr w => VectorMatch p v w
  | _, _ => False

namespace BaseMatch
variable {p q : ModelIsoCondition I J Ω} {a c : BasePoints I} {b d : BasePoints J}

theorem keep (m : BaseMatch p a b) (h : q ≤ p) : BaseMatch q a b := by
  cases a <;> cases b
  · exact h m
  · exact m
  · exact m
  · exact VectorMatch.keep m h

theorem symm (m : BaseMatch p a b) : BaseMatch p.symm b a := by
  cases a <;> cases b
  · exact ModelIsoCondition.mem_symm_graph.mpr m
  · exact m
  · exact m
  · exact VectorMatch.symm m

theorem eq_iff (h : BaseMatch p a b) (k : BaseMatch p c d) : a = c ↔ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> try contradiction
  · exact ⟨fun e => congrArg Sum.inl (p.functional _ h _ k (Sum.inl.inj e)),
      fun e => congrArg Sum.inl (p.injective _ h _ k (Sum.inl.inj e))⟩
  · constructor <;> intro e <;> cases e
  · constructor <;> intro e <;> cases e
  · exact ⟨fun e => congrArg Sum.inr ((VectorMatch.eq_iff h k).mp (Sum.inr.inj e)),
      fun e => congrArg Sum.inr ((VectorMatch.eq_iff h k).mpr (Sum.inr.inj e))⟩

theorem forth [Nonempty J] (p : ModelIsoCondition I J Ω) (a : BasePoints I) :
    ∃ (q : ModelIsoCondition I J Ω) (b : BasePoints J), q ≤ p ∧ BaseMatch q a b := by
  cases a with
  | inl i =>
    obtain ⟨q,j,qp,ij⟩ := extendIndexLeft p i
    exact ⟨q,.inl j,qp,ij⟩
  | inr u =>
    obtain ⟨q,v,qp,uv⟩ := VectorMatch.forth p u
    exact ⟨q,.inr v,qp,uv⟩

theorem back [Nonempty I] (p : ModelIsoCondition I J Ω) (b : BasePoints J) :
    ∃ (q : ModelIsoCondition I J Ω) (a : BasePoints I), q ≤ p ∧ BaseMatch q a b := by
  obtain ⟨q,a,qp,ab⟩ := forth p.symm b
  exact ⟨q.symm,a,by simpa using (ModelIsoCondition.symm_le_symm_iff.mpr qp),ab.symm⟩

theorem inl_of {a : I} (h : BaseMatch p (.inl a) b) :
    ∃ j, b = .inl j ∧ (a,j) ∈ p.graph := by
  cases b with
  | inl j => exact ⟨j,rfl,h⟩
  | inr => exact False.elim h

theorem inr_of {v : VectorGroup I} (h : BaseMatch p (.inr v) b) :
    ∃ w, b = .inr w ∧ VectorMatch p v w := by
  cases b with
  | inl => exact False.elim h
  | inr w => exact ⟨w,rfl,h⟩

private theorem forward [Nonempty I] [Nonempty J] {i : I} {j : J} (ij : (i,j) ∈ p.graph)
    {n} (r : BaseRelation Ω n) {a : Tuple (BasePoints I) n} {b : Tuple (BasePoints J) n}
    (g : ∀ l, BaseMatch p (a l) (b l)) (h : baseModel i r a) : baseModel j r b := by
  cases r with
  | index r =>
    obtain ⟨s, hs, atom⟩ := h
    have matchIdx l := inl_of ((hs l) ▸ g l)
    let t := fun l => (matchIdx l).choose
    have pair l : (s l, t l) ∈ p.graph := (matchIdx l).choose_spec.2
    refine ⟨t, fun l => (matchIdx l).choose_spec.1, ?_⟩
    have same := (indexSystem (Ω := Ω) i j).atoms ⟨p, ij, pair⟩ (.rel r id)
    exact same.mp atom
  | indexSort =>
    obtain ⟨x,hx⟩ := h
    obtain ⟨y,hy,_⟩ := inl_of (hx ▸ g 0)
    exact ⟨y,hy⟩
  | vectorSort =>
    obtain ⟨x,hx⟩ := h
    obtain ⟨y,hy,_⟩ := inr_of (hx ▸ g 0)
    exact ⟨y,hy⟩
  | coefficient v =>
    obtain ⟨u,x,hu,hx,coef⟩ := h
    obtain ⟨w,hw,uw⟩ := inr_of (hu ▸ g 0)
    obtain ⟨y,hy,xy⟩ := inl_of (hx ▸ g 1)
    exact ⟨w,y,hw,hy,(uw.coeff xy).symm.trans coef⟩

theorem base_iff [Nonempty I] [Nonempty J] {i : I} {j : J} (ij : (i,j) ∈ p.graph)
    {n} (r : BaseRelation Ω n) {a b} (h : ∀ l, BaseMatch p (a l) (b l)) :
    baseModel i r a ↔ baseModel j r b :=
  ⟨forward ij r h, forward (ModelIsoCondition.mem_symm_graph.mpr ij) r (fun l => (h l).symm)⟩

/-- Match an entire tuple of nonnegative coefficients in the named transition language. -/
theorem letterTuple {n} {s : Tuple (BasePoints I) n} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p (s l) (t l)) (a : Fin n → Letter I)
    (ha : ∀ l, s l = .inr (a l).val) :
    ∃ b : Fin n → Letter J, (∀ l, t l = .inr (b l).val) ∧
      WordMatch p (List.ofFn a) (List.ofFn b) := by
  have one l : ∃ b : Letter J, t l = .inr b.val ∧ LetterMatch p (a l) b := by
    obtain ⟨v, hv, hm⟩ := inr_of ((ha l) ▸ m l)
    exact ⟨⟨v, (VectorMatch.zero.le_iff hm).mp (a l).property⟩,hv,hm⟩
  let b := fun l => (one l).choose
  refine ⟨b,fun l => (one l).choose_spec.1,?_⟩
  have pair : ∀ {k} (f : Fin k → Letter I) (g : Fin k → Letter J), (∀ l, LetterMatch p (f l) (g l)) →
      WordMatch p (List.ofFn f) (List.ofFn g) := by
    intro k; induction k with
    | zero => intro f g h; simp only [List.ofFn_zero]; exact .nil
    | succ k ih =>
      intro f g h
      rw [List.ofFn_succ,List.ofFn_succ]
      exact .cons (h 0) (ih _ _ (fun l => h l.succ))
  exact pair a b (fun l => (one l).choose_spec.2)

end BaseMatch
end KnightModel.RankTwo.Scott
