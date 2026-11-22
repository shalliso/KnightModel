import KnightModel.Transfinite.MatchState
import KnightModel.RankTwo.Alphabet

/-! # Transport of finite-support colex vectors on matched old index tuples -/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}

structure VectorMatch (p : F.State) (u : VectorGroup I) (v : VectorGroup J) :
    Prop where
  coeff : ∀ {i j}, (i, j) ∈ p.graph → u i = v j
  leftZero : ∀ i, i ∉ p.dom → u i = 0
  rightZero : ∀ j, j ∉ p.ran → v j = 0

namespace VectorMatch

variable {p q : F.State} {a c : VectorGroup I} {b d : VectorGroup J}

theorem keep (H : VectorMatch p a b) (hq : q ≤ p) : VectorMatch q a b where
  coeff := by
    intro i j ij
    by_cases hi : i ∈ p.dom
    · obtain ⟨k, ik⟩ := hi
      have e : k = j := q.functional _ (hq ik) _ ij rfl
      exact e ▸ H.coeff ik
    · have hj : j ∉ p.ran := by
        rintro ⟨k, kj⟩
        have e : k = i := q.injective _ (hq kj) _ ij rfl
        exact hi ⟨j, e ▸ kj⟩
      rw [H.leftZero i hi, H.rightZero j hj]
  leftZero i hi := H.leftZero i (fun ⟨j, h⟩ => hi ⟨j, hq h⟩)
  rightZero j hj := H.rightZero j (fun ⟨i, h⟩ => hj ⟨i, hq h⟩)

theorem symm (H : VectorMatch p a b) : VectorMatch p.symm b a where
  coeff ij := (H.coeff (OrderedBF.State.mem_symm_graph.mp ij)).symm
  leftZero j h := H.rightZero j (fun hj => h (p.mem_dom_symm_iff_mem_ran.mpr hj))
  rightZero i h := H.leftZero i (fun ⟨j, hi⟩ => h ⟨j, OrderedBF.State.mem_symm_graph.mpr hi⟩)

theorem zero : VectorMatch p 0 0 := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem add (H : VectorMatch p a b) (K : VectorMatch p c d) :
    VectorMatch p (a+c) (b+d) where
  coeff := fun ij => congrArg₂ (·+·) (H.coeff ij) (K.coeff ij)
  leftZero i hi := by change a i + c i = 0; rw [H.leftZero i hi, K.leftZero i hi, add_zero]
  rightZero j hj := by change b j + d j = 0; rw [H.rightZero j hj, K.rightZero j hj, add_zero]

theorem sub (H : VectorMatch p a b) (K : VectorMatch p c d) :
    VectorMatch p (a-c) (b-d) where
  coeff := fun ij => congrArg₂ (·-·) (H.coeff ij) (K.coeff ij)
  leftZero i hi := by change a i - c i = 0; rw [H.leftZero i hi, K.leftZero i hi, sub_self]
  rightZero j hj := by change b j - d j = 0; rw [H.rightZero j hj, K.rightZero j hj, sub_self]

theorem single {i j} (h : (i, j) ∈ p.graph) (r : ℚ) :
    VectorMatch p (toColex (Finsupp.single i r)) (toColex (Finsupp.single j r)) where
  coeff := by
    intro k l kl
    by_cases e : k = i
    · subst k
      have f : l = j := p.functional _ kl _ h rfl
      subst l
      simp
    · have ne : l ≠ j := fun f => e (p.injective _ kl _ h f)
      simp [Finsupp.single_eq_of_ne e, Finsupp.single_eq_of_ne ne]
  leftZero k hk := Finsupp.single_eq_of_ne (fun e => hk (e ▸ ⟨j,h⟩))
  rightZero l hl := Finsupp.single_eq_of_ne (fun e => hl (e ▸ ⟨i,h⟩))

private theorem lt_forward (H : VectorMatch p a b) (K : VectorMatch p c d) (ac : a < c) :
    b < d := by
  obtain ⟨i, above, diff⟩ := Finsupp.Colex.lt_iff.mp ac
  have hi : i ∈ p.dom := by
    by_contra hi
    rw [H.leftZero i hi, K.leftZero i hi] at diff
    exact lt_irrefl _ diff
  obtain ⟨j, ij⟩ := hi
  refine Finsupp.Colex.lt_iff.mpr ⟨j, ?_, (H.coeff ij) ▸ (K.coeff ij) ▸ diff⟩
  intro l jl
  by_cases hl : l ∈ p.ran
  · obtain ⟨k, kl⟩ := hl
    have ik : i < k := lt_of_not_ge fun ki =>
      jl.not_ge ((p.toPartialIso.order_pres_iff kl ij).mp ki)
    exact (H.coeff kl).symm.trans ((above k ik).trans (K.coeff kl))
  · rw [H.rightZero l hl, K.rightZero l hl]

theorem lt_iff (H : VectorMatch p a b) (K : VectorMatch p c d) : a < c ↔ b < d :=
  ⟨H.lt_forward K, H.symm.lt_forward K.symm⟩

theorem le_iff (H : VectorMatch p a b) (K : VectorMatch p c d) : a ≤ c ↔ b ≤ d := by
  rw [← not_lt, ← not_lt, K.lt_iff H]

theorem eq_iff (H : VectorMatch p a b) (K : VectorMatch p c d) : a = c ↔ b = d := by
  rw [le_antisymm_iff, le_antisymm_iff, H.le_iff K, K.le_iff H]

private theorem coversFinite (p : F.State) (s : Finset I) :
    ∃ q : F.State, q ≤ p ∧ ∀ i ∈ s, i ∈ q.dom := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨p, le_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q, qp, dom⟩ := ih
    obtain ⟨r, b, rq, ab⟩ := q.extendIndexLeft a
    refine ⟨r, rq.trans qp, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨b, ab⟩
    · obtain ⟨j, ij⟩ := dom i hi
      exact ⟨j, rq ij⟩

theorem forth (p : F.State) (a : VectorGroup I) :
    ∃ (q : F.State) (b : VectorGroup J), q ≤ p ∧ VectorMatch q a b := by
  classical
  obtain ⟨q, qp, dom⟩ := coversFinite p (ofColex a).support
  let f (j : J) : ℚ := if h : j ∈ q.ran then a ((OrderedBF.State.mem_ran_iff.mp h).choose) else 0
  have fr j (h : j ∉ q.ran) : f j = 0 := dif_neg h
  let b := Finsupp.onFinset q.finite_ran.toFinset f (fun j hj => by
    apply (Set.Finite.mem_toFinset q.finite_ran).mpr
    exact Classical.byContradiction (fun h => hj (fr j h)))
  refine ⟨q, toColex b, qp, ?_, ?_, ?_⟩
  · intro i j ij
    change a i = f j
    have hj : j ∈ q.ran := ⟨i, ij⟩
    simp only [f, dif_pos hj]
    exact congrArg a (q.injective _ ij _ (OrderedBF.State.mem_ran_iff.mp hj).choose_spec rfl)
  · intro i hi
    exact Classical.byContradiction (fun h => hi (dom i (Finsupp.mem_support_iff.mpr h)))
  · exact fr

theorem back (p : F.State) (b : VectorGroup J) :
    ∃ (q : F.State) (a : VectorGroup I), q ≤ p ∧ VectorMatch q a b := by
  obtain ⟨q, a, qp, h⟩ := forth p.symm b
  exact ⟨q.symm, a, OrderedBF.State.reverse_refines qp, h.symm⟩

end VectorMatch
end KnightModel.Transfinite
