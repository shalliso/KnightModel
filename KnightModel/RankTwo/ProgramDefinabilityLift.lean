import KnightModel.RankTwo.ProgramDefinabilitySelection

/-! # Semilinear word graphs over a vector subalphabet -/

namespace KnightModel.RankTwo.Semilinear

variable {A V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V]
variable {n m : Nat}

/-- Finite graph tests performed in an allowed subalphabet, interpreted in the
ambient ordered vector space using the graph of the letter inclusion. -/
abbrev LiftDefinable (j : A → V) (R : (Fin n → V) → List A → List A → Prop) :=
  GraphDefinable (fun p => liftWordGraph j (R p))

namespace GraphDefinable

theorem congr {R S : (Fin n → V) → List V → List V → Prop} (h : GraphDefinable R)
    (eqv : ∀ p x y, R p x y ↔ S p x y) : GraphDefinable S := by
  intro k s x y
  convert h s x y using 1
  ext p
  exact (eqv _ _ _).symm

theorem parameters {R : (Fin n → V) → List V → List V → Prop} (h : GraphDefinable R)
    (t : Fin n → Term V m) : GraphDefinable (fun p => R (evalTuple t p)) := by
  intro k s x y
  simpa only [eval_subst_tuple] using h (fun i => (t i).subst s) x y

end GraphDefinable

namespace LiftDefinable

variable {j : A → V} {R S : (Fin n → V) → List A → List A → Prop}

theorem congr (h : LiftDefinable j R) (eqv : ∀ p x y, R p x y ↔ S p x y) : LiftDefinable j S := by
  apply GraphDefinable.congr (R := fun p => liftWordGraph j (R p)) h
  intro p x y
  unfold liftWordGraph
  simp only [eqv]

theorem parameters (h : LiftDefinable j R) (t : Fin n → Term V m) :
    LiftDefinable j (fun p => R (evalTuple t p)) :=
  GraphDefinable.parameters (R := fun p => liftWordGraph j (R p)) h t

theorem inv (h : LiftDefinable j R) : LiftDefinable j (fun p x y => R p y x) := by
  apply GraphDefinable.congr (R := fun p x y => liftWordGraph j (R p) y x)
    (GraphDefinable.inv (R := fun p => liftWordGraph j (R p)) h)
  intro p x y
  constructor <;> rintro ⟨u,v,hu,hv,r⟩ <;> exact ⟨v,u,hv,hu,r⟩

theorem union (h : LiftDefinable j R) (g : LiftDefinable j S) :
    LiftDefinable j (fun p x y => R p x y ∨ S p x y) := by
  apply GraphDefinable.congr (R := fun p x y => liftWordGraph j (R p) x y ∨ liftWordGraph j (S p) x y)
    (GraphDefinable.union (R := fun p => liftWordGraph j (R p)) (S := fun p => liftWordGraph j (S p)) h g)
  intro p x y
  constructor
  · rintro (⟨u,v,hu,hv,r⟩ | ⟨u,v,hu,hv,s⟩)
    · exact ⟨u,v,hu,hv,Or.inl r⟩
    · exact ⟨u,v,hu,hv,Or.inr s⟩
  · rintro ⟨u,v,hu,hv,r | s⟩
    · exact Or.inl ⟨u,v,hu,hv,r⟩
    · exact Or.inr ⟨u,v,hu,hv,s⟩

/-- Quantify a bounded intermediate subalphabet word. Every candidate is
already accepted by both lifted graphs, so all its letters are valid. -/
theorem seq (qe : HeadElimination V) (hj : Function.Injective j)
    (h : LiftDefinable j R) (g : LiftDefinable j S) (b : Nat) (bound : ∀ p, PrefixBounds (R p) b) :
    LiftDefinable j (fun p x y => ∃ z, R p x z ∧ S p z y) := by
  have size : ∀ p x z, liftWordGraph j (R p) x z → z.length ≤ x.length+b := by
    rintro p _ _ ⟨u,v,rfl,rfl,r⟩
    simpa using ((bound p).sizes r).2
  apply GraphDefinable.congr (R := fun p x y => ∃ z, liftWordGraph j (R p) x z ∧ liftWordGraph j (S p) z y)
    (GraphDefinable.seq_of_length (R := fun p => liftWordGraph j (R p)) (S := fun p => liftWordGraph j (S p)) qe h g b size)
  intro p x y
  constructor
  · rintro ⟨z, ⟨u,v,hu,hv,r⟩, w,t,hw,ht,s⟩
    obtain rfl : v = w := List.map_injective_iff.mpr hj (hv.trans hw.symm)
    exact ⟨u,t,hu,ht,v,r,s⟩
  · rintro ⟨u,v,hu,hv,w,r,s⟩
    exact ⟨w.map j, ⟨u,w,hu,rfl,r⟩, ⟨w,v,rfl,hv,s⟩⟩

end LiftDefinable
end KnightModel.RankTwo.Semilinear
