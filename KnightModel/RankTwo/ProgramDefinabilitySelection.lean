import KnightModel.RankTwo.ProgramDefinabilityFormula
import KnightModel.RankTwo.SemilinearSelection

/-! # Parameter recovery from the graph on an embedded word alphabet -/

namespace KnightModel.RankTwo

/-- View a word relation on the allowed alphabet as a relation on ambient
vectors. Every accepted word in the latter relation uses only allowed letters. -/
def liftWordGraph {A V : Type*} (j : A → V) (R : List A → List A → Prop) (x y : List V) : Prop :=
  ∃ u v, u.map j = x ∧ v.map j = y ∧ R u v

theorem liftWordGraph_map {A V : Type*} {j : A → V} (hj : Function.Injective j)
    (R : List A → List A → Prop) (x y : List A) :
    liftWordGraph j R (x.map j) (y.map j) ↔ R x y := by
  constructor
  · rintro ⟨z,w,hz,hw,r⟩
    exact (List.map_injective_iff.mpr hj hz) ▸ (List.map_injective_iff.mpr hj hw) ▸ r
  · exact fun h => ⟨x,y,rfl,rfl,h⟩

/-- Tests on uniformly short vectors detect equality on all words in the
subalphabet. No extension to a map on words using forbidden letters is needed. -/
theorem lifted_graph_test {A V : Type*} {j : A → V} (hj : Function.Injective j)
    {R S : List A → List A → Prop} {a b : Nat} (hr : PrefixBounds R a) (hs : PrefixBounds S b) :
    (∀ x y, R x y ↔ S x y) ↔ ∀ x y : List V,
      x.length ≤ 2 * max a b → y.length ≤ 2 * max a b → (liftWordGraph j R x y ↔ liftWordGraph j S x y) := by
  constructor
  · intro eqv x y _ _
    constructor
    · rintro ⟨u,v,hu,hv,h⟩; exact ⟨u,v,hu,hv,(eqv u v).mp h⟩
    · rintro ⟨u,v,hu,hv,h⟩; exact ⟨u,v,hu,hv,(eqv u v).mpr h⟩
  · intro test
    apply ((hr.mono (Nat.le_max_left a b)).ext_iff (hs.mono (Nat.le_max_right a b))).mpr
    intro x y hx hy
    simpa only [liftWordGraph_map hj] using test (x.map j) (y.map j) (by simpa using hx) (by simpa using hy)

namespace Semilinear

open UnaryChoice

variable {A V : Type*} [AddCommGroup V] [Module ℚ V] [LinearOrder V]

/-- Graph equality for two different schemes in a nonnegative-letter order,
with the right-hand parameter tuple fixed. -/
theorem lifted_equality_fiber {n m} {j : A → V} (hj : Function.Injective j)
    {R : (Fin n → V) → List A → List A → Prop} {S : (Fin m → V) → List A → List A → Prop}
    (qe : HeadElimination V) (h : GraphDefinable (fun p => liftWordGraph j (R p)))
    (g : GraphDefinable (fun p => liftWordGraph j (S p))) (q : Fin m → V) (a b : Nat)
    (hr : ∀ p, PrefixBounds (R p) a) (hs : PrefixBounds (S q) b) :
    Definable {p | ∀ x y, R p x y ↔ S q x y} :=
  GraphDefinable.equality_fiber_of_test (R := fun p => liftWordGraph j (R p))
    (T := fun p => liftWordGraph j (S p)) qe h g q (2 * max a b) _ (fun p => lifted_graph_test hj (hr p) hs)

variable [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] [DenselyOrdered V]

/-- The fiber of parameters presenting one graph contains a tuple fixed by its
entire setwise stabilizer, acting on the original ordered vector space. -/
theorem exists_fixed_graph_parameters {G : Type*} [Group G] [MulAction G V]
    {n m} {j : A → V} (hj : Function.Injective j)
    {R : (Fin n → V) → List A → List A → Prop} {S : (Fin m → V) → List A → List A → Prop}
    {P : Samples V} (samples : AffineSamples P) (iso : G → V ≃o V)
    (action : ∀ g x, iso g x = g • x) (pres : ∀ g, Preserves (P := P) (iso g))
    (h : GraphDefinable (fun p => liftWordGraph j (R p))) (g : GraphDefinable (fun p => liftWordGraph j (S p)))
    (q : Fin m → V) (a b : Nat) (hr : ∀ p, PrefixBounds (R p) a) (hs : PrefixBounds (S q) b)
    (nonempty : ∃ p, ∀ x y, R p x y ↔ S q x y) :
    ∃ p, (∀ x y, R p x y ↔ S q x y) ∧
      ∀ f : G, (∀ t, (∀ x y, R t x y ↔ S q x y) ↔ (∀ x y, R (fun i => f • t i) x y ↔ S q x y)) →
        ∀ i, f • p i = p i :=
  Definable.exists_fixed samples iso action pres
    (lifted_equality_fiber hj (Definable.exists_head samples) h g q a b hr hs) nonempty

end Semilinear
end KnightModel.RankTwo
