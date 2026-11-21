import KnightModel.RankTwo.ConcreteModel
import KnightModel.RankTwo.ScottSchemes
import KnightModel.RankTwo.ScottBaseMatches

/-! # Matching the partial evaluation of a named frame relation -/

namespace KnightModel.RankTwo.Concrete

open Scott

variable {I J Ω : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]
variable {p : ModelIsoCondition I J Ω}

theorem match_ofFn {n : ℕ} {u : Fin n → Letter I} {v : Fin n → Letter J}
    (h : ∀ k, LetterMatch p (u k) (v k)) :
    WordMatch p (List.ofFn u) (List.ofFn v) := by
  induction n with
  | zero => simp [WordMatch]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (ih (fun k => h k.succ))

private abbrev pack {X : Type} [LinearOrder X] {n : ℕ} (u : Fin n → Letter X) :
    Tuple (BasePoints X) n := fun k => Sum.inr (u k).val

/-- A whole tuple of nonnegative-vector arguments has a matching tuple of
nonnegative-vector arguments. This holds already in the current position. -/
theorem match_arguments {n} {u : Fin n → Letter I} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p ((pack u) l) (t l)) :
    ∃ v : Fin n → Letter J, t = pack v ∧ WordMatch p (List.ofFn u) (List.ofFn v) := by
  classical
  have h (l : Fin n) := BaseMatch.inr_of (m l)
  let v (l : Fin n) : Letter J := ⟨(h l).choose,
    (VectorMatch.zero.le_iff (h l).choose_spec.2).mp (u l).property⟩
  exact ⟨v,funext fun l => (h l).choose_spec.1,match_ofFn (fun l => (h l).choose_spec.2)⟩

private theorem none_if_not_arguments {n : ℕ} {i : I} {k : Name n}
    {s : Tuple (BasePoints I) n} (hs : ¬∃ u : Fin n → Letter I, s = pack u) :
    run i k s = none := by
  cases h : run i k s with
  | none => rfl
  | some c =>
    obtain ⟨u,hu,_⟩ := run_eq_some.mp h
    exact (hs ⟨u,funext hu⟩).elim

variable [Nonempty I] [Nonempty J]

private theorem run_match_letters {n : ℕ} {i : I} {j : J} (A : IntervalMatches (Ω := Ω) i j)
    (mark : (i,j) ∈ p.graph) (k : Name n) (u : Fin n → Letter I) (v : Fin n → Letter J)
    (uv : WordMatch p (List.ofFn u) (List.ofFn v)) :
    Option.Rel (fun c e => GraphMatch p (fun x y => c.val x = y) (fun x y => e.val x = y))
      (run i k (pack u)) (run j k (pack v)) := by
  have graphs := schemeGraph_match A mark k.val uv
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
theorem run_matches {n : ℕ} {i : I} {j : J} (A : IntervalMatches (Ω := Ω) i j)
    (mark : (i,j) ∈ p.graph) (k : Name n) {s : Tuple (BasePoints I) n} {t : Tuple (BasePoints J) n}
    (m : ∀ l, BaseMatch p (s l) (t l)) :
    Option.Rel (fun c e => GraphMatch p (fun x y => c.val x = y) (fun x y => e.val x = y))
      (run i k s) (run j k t) := by
  classical
  by_cases h : ∃ u : Fin n → Letter I, s = pack u
  · obtain ⟨u,rfl⟩ := h
    obtain ⟨v,rfl,uv⟩ := match_arguments m
    exact run_match_letters A mark k u v uv
  · have h' : ¬∃ v : Fin n → Letter J, t = pack v := by
      rintro ⟨v,rfl⟩
      obtain ⟨u,hu,_⟩ := match_arguments (p := p.symm) (fun l => (m l).symm)
      exact h ⟨u,hu⟩
    rw [none_if_not_arguments h, none_if_not_arguments h']
    exact .none

end KnightModel.RankTwo.Concrete
