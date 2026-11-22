import KnightModel.Transfinite.MatchWords
import KnightModel.RankTwo.BaseLanguage

/-! # Moves on the combined old-index and vector sorts -/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}

def BaseMatch (p : F.State) : BasePoints I → BasePoints J → Prop
  | .inl i, .inl j => (i,j) ∈ p.graph
  | .inr v, .inr w => VectorMatch p v w
  | _, _ => False

namespace BaseMatch
variable {p q : F.State} {a c : BasePoints I} {b d : BasePoints J}

theorem keep (m : BaseMatch p a b) (h : q ≤ p) : BaseMatch q a b := by
  cases a <;> cases b
  · exact h m
  · exact m
  · exact m
  · exact VectorMatch.keep m h

theorem symm (m : BaseMatch p a b) : BaseMatch p.symm b a := by
  cases a <;> cases b
  · exact OrderedBF.State.mem_symm_graph.mpr m
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

theorem forth (p : F.State) (a : BasePoints I) :
    ∃ (q : F.State) (b : BasePoints J), q ≤ p ∧ BaseMatch q a b := by
  cases a with
  | inl i =>
    obtain ⟨q,j,qp,ij⟩ := p.extendIndexLeft i
    exact ⟨q,.inl j,qp,ij⟩
  | inr u =>
    obtain ⟨q,v,qp,uv⟩ := VectorMatch.forth p u
    exact ⟨q,.inr v,qp,uv⟩

theorem back (p : F.State) (b : BasePoints J) :
    ∃ (q : F.State) (a : BasePoints I), q ≤ p ∧ BaseMatch q a b := by
  obtain ⟨q,a,qp,ab⟩ := forth p.symm b
  exact ⟨q.symm,a,OrderedBF.State.reverse_refines qp,ab.symm⟩

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

/-- Match an entire tuple of nonnegative coefficients in the named transition language. -/
theorem letterTuple {n} {s : Tuple (BasePoints I) n} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p (s l) (t l)) (a : Fin n → Letter I)
    (ha : ∀ l, s l = .inr (a l).val) :
    ∃ b : Fin n → Letter J, (∀ l, t l = .inr (b l).val) ∧
      WordMatch p (List.ofFn a) (List.ofFn b) := by
  have one l : ∃ b : Letter J, t l = .inr b.val ∧ LetterMatch p (a l) b := by
    obtain ⟨v, hv, hm⟩ := inr_of ((ha l) ▸ m l)
    exact ⟨⟨v, (VectorMatch.zero.le_iff hm).mp (a l).property⟩,hv,hm⟩
  choose b hb pair using one
  refine ⟨b,hb,List.forall₂_iff_get.mpr ⟨by simp,?_⟩⟩
  intro i h₁ h₂
  simpa using pair ⟨i,by simpa using h₁⟩

end BaseMatch
end KnightModel.Transfinite
