import KnightModel.RankTwo.ScottLanguage
import KnightModel.RankTwo.RankModel
import Mathlib.Data.Fin.Tuple.Basic

/-! # Recovering frame comparison and transition fibers from named relations -/

namespace KnightModel.RankTwo.Scott

variable {P C F : Type*} {B K : ℕ → Type*} {A : FrameAction C F}
    (T : FrameInterpretation B K P A)

namespace FrameAction

def Below (A : FrameAction C F) (u v : F) : Prop := ∃ c, A.act v c = u

theorem below_total (A : FrameAction C F) (u v : F) : A.Below u v ∨ A.Below v u := by
  rcases A.compare u v with h | ⟨c, _, hc⟩
  · exact Or.inr h
  · exact Or.inl ⟨c, hc⟩

end FrameAction

namespace FrameInterpretation

def Transition {n} (k : K n) (u v : F) (p : Fin n → P) : Prop :=
  ∃ c, T.run k p = some c ∧ A.act v c = u

theorem transition_functional {n} (k : K n) (v : F) (p : Fin n → P) {u u' : F}
    (h : T.Transition k u v p) (h' : T.Transition k u' v p) : u = u' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact congrArg (A.act v) (Option.some.inj (hc.symm.trans hc'))

private def pairArgs (u v : F) : Tuple (P ⊕ F) 2 := Fin.cons (.inr u) (fun _ => .inr v)

private def transArgs {n} (u v : F) (p : Fin n → P) : Tuple (P ⊕ F) (n+2) :=
  Fin.cons (.inr u) (Fin.cons (.inr v) (Sum.inl ∘ p))

theorem model_below_iff (u v : F) : T.model .below (pairArgs u v) ↔ A.Below u v := by
  constructor
  · rintro ⟨z, c, hu, hv⟩
    obtain rfl : v = z := Sum.inr.inj hv
    exact ⟨c, (Sum.inr.inj hu).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨v, c, rfl, rfl⟩

theorem model_transition_iff {n} (k : K n) (u v : F) (p : Fin n → P) :
    T.model (.transition k) (transArgs u v p) ↔ T.Transition k u v p := by
  constructor
  · rintro ⟨q, c, z, hp, hc, hu, hv⟩
    obtain rfl : v = z := Sum.inr.inj hv
    have hqp : p = q := funext fun i => Sum.inl.inj (hp i)
    exact ⟨c, hqp ▸ hc, (Sum.inr.inj hu).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨p, c, v, fun _ => rfl, hc, rfl, rfl⟩

/-- Preservation of the named binary relation gives full-group invariance
of the relative order on frames. -/
theorem invariant_below (g : ↥(automorphismGroup T.model)) (f : F → F)
    (hf : ∀ x, Sum.inr (f x) = g.val (.inr x)) (u v : F) :
    A.Below u v ↔ A.Below (f u) (f v) := by
  rw [← T.model_below_iff u v, ← T.model_below_iff (f u) (f v)]
  have he : g.val ∘ pairArgs u v = pairArgs (f u) (f v) := by
    funext i
    exact Fin.cases (hf u).symm (fun _ => (hf v).symm) i
  exact he ▸ g.property .below (pairArgs u v)

/-- The parameter sub-sort may be a proper summand of the whole base sort. -/
theorem invariant_transition {V : Type*} (par : V → P)
    (g : ↥(automorphismGroup T.model)) (f : F → F) (e : V → V)
    (hf : ∀ x, Sum.inr (f x) = g.val (.inr x))
    (he : ∀ x, Sum.inl (par (e x)) = g.val (.inl (par x)))
    {n} (k : K n) (u v : F) (p : Fin n → V) :
    T.Transition k u v (par ∘ p) ↔ T.Transition k (f u) (f v) (par ∘ e ∘ p) := by
  rw [← T.model_transition_iff k u v, ← T.model_transition_iff k (f u) (f v)]
  have eqn : g.val ∘ transArgs u v (par ∘ p) = transArgs (f u) (f v) (par ∘ e ∘ p) := by
    funext i
    exact Fin.cases (hf u).symm (fun j => Fin.cases (hf v).symm (fun k => (he (p k)).symm) j) i
  exact eqn ▸ g.property (.transition k) (transArgs u v (par ∘ p))

end FrameInterpretation
end KnightModel.RankTwo.Scott
