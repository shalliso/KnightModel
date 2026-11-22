import KnightModel.Transfinite.MatchIntervals
import KnightModel.Transfinite.MatchBase
import KnightModel.RankTwo.ConcreteModel

/-! # Evaluation of an arbitrary named coordinate transfers over old matches -/

namespace KnightModel.Transfinite

open RankTwo Scott Concrete

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}
variable {p : F.State}

private abbrev pack {X : Type} [LinearOrder X] {n : ℕ} (u : Fin n → Letter X) :
    Tuple (BasePoints X) n := fun k => Sum.inr (u k).val

/-- A whole tuple of nonnegative-vector arguments has a matching tuple of
nonnegative-vector arguments. This holds already in the current position. -/
theorem match_arguments {n} {u : Fin n → Letter I} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p ((pack u) l) (t l)) :
    ∃ v : Fin n → Letter J, t = pack v ∧ WordMatch p (List.ofFn u) (List.ofFn v) := by
  obtain ⟨v,he,word⟩ := BaseMatch.letterTuple m u (fun _ => rfl)
  exact ⟨v,funext he,word⟩

private theorem none_if_not_arguments {n : ℕ} {i : I} {k : Name n}
    {s : Tuple (BasePoints I) n} (hs : ¬∃ u : Fin n → Letter I, s = pack u) :
    run i k s = none := by
  cases h : run i k s with
  | none => rfl
  | some c =>
    obtain ⟨u,hu,_⟩ := run_eq_some.mp h
    exact (hs ⟨u,funext hu⟩).elim


private theorem run_match_letters {n : ℕ} {i : I} {j : J} 
    (mark : (i,j) ∈ p.graph) (k : Name n) (u : Fin n → Letter I) (v : Fin n → Letter J)
    (uv : WordMatch p (List.ofFn u) (List.ofFn v)) :
    Option.Rel (fun c e => GraphMatch p (fun x y => c.val x = y) (fun x y => e.val x = y))
      (run i k (pack u)) (run j k (pack v)) := by
  have graphs := orderedScheme_match mark k.val uv
  have exist_iff : (∃ c, run i k (pack u) = some c) ↔ ∃ e, run j k (pack v) = some e :=
    (run_exists_iff i k u).trans (graphs.fullInitial.trans (run_exists_iff j k v).symm)
  cases h : run i k (pack u) with
  | none =>
    cases h' : run j k (pack v) with
    | none => exact .none
    | some e =>
      obtain ⟨c,hc⟩ := exist_iff.mpr ⟨e,h'⟩
      rw [h] at hc
      cases hc
  | some c =>
    obtain ⟨e,he⟩ := exist_iff.mp ⟨c,h⟩
    rw [he]
    apply Option.Rel.some
    have left := (run_letters_iff i k u c).mp h
    have right := (run_letters_iff j k v e).mp he
    intro q qp x y x' y' xx yy
    exact (left x y).symm.trans ((graphs qp xx yy).trans (right x' y'))

/-- Both evaluations reject together, or they give coordinate maps whose
graphs match at every finite extension of the current index position. -/
theorem run_matches {n : ℕ} {i : I} {j : J} 
    (mark : (i,j) ∈ p.graph) (k : Name n) {s : Tuple (BasePoints I) n} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p (s l) (t l)) :
    Option.Rel (fun c e => GraphMatch p (fun x y => c.val x = y) (fun x y => e.val x = y))
      (run i k s) (run j k t) := by
  classical
  by_cases h : ∃ u : Fin n → Letter I, s = pack u
  · obtain ⟨u,rfl⟩ := h
    obtain ⟨v,rfl,uv⟩ := match_arguments m
    exact run_match_letters mark k u v uv
  · have h' : ¬∃ v : Fin n → Letter J, t = pack v := by
      rintro ⟨v,rfl⟩
      obtain ⟨u,hu,_⟩ := match_arguments (p := p.symm) (fun l => (m l).symm)
      exact h ⟨u,hu⟩
    rw [none_if_not_arguments h, none_if_not_arguments h']
    exact .none

end KnightModel.Transfinite
