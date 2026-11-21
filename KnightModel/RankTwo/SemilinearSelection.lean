import KnightModel.RankTwo.SemilinearQE
import KnightModel.RankTwo.RankSelection

/-! # Stabilizer-fixed selection in semilinear vector fibers -/

namespace KnightModel.RankTwo.Semilinear

open UnaryChoice

variable {V : Type*} {n : ℕ} [AddCommGroup V] [Module ℚ V] [LinearOrder V]
    [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V]

def UnaryDefinable (S : Set V) : Prop := Definable {p : Fin 1 → V | p 0 ∈ S}

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem Definable.tailFiber {S : Set (Fin (n+1) → V)} (h : Definable S) (z : V) :
    Definable (RankTwo.tailFiber S z) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.plug (.const z), fun p => (hφ _).trans (φ.holds_plug (.const z) p).symm⟩

/-- Interchanging the first two vector variables exposes the first hidden
variable of a head projection to the one-variable elimination theorem. -/
private def swapIndices (i : Fin (n+2)) : Fin (n+2) :=
  Fin.cases 1 (Fin.cases 0 (fun j => j.succ.succ)) i

omit [AddCommGroup V] [Module ℚ V] [LinearOrder V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
private theorem swap_cons (x y : V) (p : Fin n → V) :
    (Fin.cons y (Fin.cons x p)) ∘ swapIndices = Fin.cons x (Fin.cons y p) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases <;> rfl

theorem Definable.headProjection {P : Samples V} (A : AffineSamples P) :
    ∀ {n : ℕ} {S : Set (Fin (n+1) → V)}, Definable S → UnaryDefinable (RankTwo.headProjection S) := by
  intro n
  induction n with
  | zero =>
    rintro S ⟨φ, hφ⟩
    refine ⟨φ, fun p => ?_⟩
    change (∃ t : Fin 0 → V, Fin.cons (p 0) t ∈ S) ↔ φ.Holds p
    have he (t : Fin 0 → V) : Fin.cons (p 0) t = p := by
      funext i
      exact Fin.cases (by simp) (fun j => Fin.elim0 j) i
    exact ⟨fun ⟨t, ht⟩ => (hφ p).mp (he t ▸ ht),
      fun hp => ⟨Fin.elim0, (he Fin.elim0).symm ▸ (hφ p).mpr hp⟩⟩
  | succ n ih =>
    intro S h
    let T : Set (Fin (n+1) → V) := {p | ∃ y : V, (Fin.cons y p ∘ swapIndices) ∈ S}
    have hT : Definable T := by
      exact Definable.exists_head A (h.subst (fun i => .var (swapIndices i)))
    have same : RankTwo.headProjection T = RankTwo.headProjection S := by
      ext x
      change (∃ t : Fin n → V, ∃ y : V, (Fin.cons y (Fin.cons x t) ∘ swapIndices) ∈ S) ↔
        ∃ t : Fin (n+1) → V, Fin.cons x t ∈ S
      constructor
      · rintro ⟨t, y, h⟩
        exact ⟨Fin.cons y t, swap_cons x y t ▸ h⟩
      · rintro ⟨t, ht⟩
        exact ⟨Fin.tail t, t 0, by simpa only [swap_cons, Fin.cons_self_tail] using ht⟩
    exact same ▸ ih hT

/-- Unary semilinear sets are monochromatic on the finitely many cells cut
out by the thresholds of their defining predicates. -/
theorem UnaryDefinable.decomposed (P : Samples V) {S : Set V} (h : UnaryDefinable S) :
    Decomposed S := by
  obtain ⟨φ, hφ⟩ := h
  let p : Fin 0 → V := Fin.elim0
  apply decomposed_of_thresholds P (φ.cuts.map (·.eval p)) S
  intro x y hc
  exact (hφ (Fin.cons x p)).trans ((φ.holds_sameCell p x y hc).trans (hφ (Fin.cons y p)).symm)

/-- Every nonempty semilinear parameter fiber contains a tuple fixed by all the
order-preserving action elements that preserve both that fiber and the sampling operations. -/
theorem Definable.exists_fixed [DenselyOrdered V] {G : Type*} [Group G] [MulAction G V]
    {P : Samples V} (A : AffineSamples P) (iso : G → V ≃o V)
    (action : ∀ g x, iso g x = g • x) (pres : ∀ g, Preserves (P := P) (iso g))
    {S : Set (Fin n → V)} (h : Definable S) (hne : S.Nonempty) :
    ∃ p ∈ S, ∀ g : G, (∀ q, q ∈ S ↔ (fun j => g • q j) ∈ S) → ∀ j, g • p j = p j := by
  apply tuple_stabilizer_fixed_selection UnaryDefinable (fun _ => Definable)
    (fun _ _ => Definable.headProjection A) (fun _ _ z hS => hS.tailFiber z) _ n S h hne
  intro T hT hneT
  obtain ⟨z, hz, fixed⟩ := UnaryChoice.exists_fixed P (hT.decomposed P) hneT
  refine ⟨z, hz, ?_⟩
  intro g hg
  simpa only [action] using fixed (iso g) (pres g) (fun w => by simpa only [action] using hg w)

end KnightModel.RankTwo.Semilinear
