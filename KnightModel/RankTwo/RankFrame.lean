import KnightModel.RankTwo.Rank
import KnightModel.Model.Basic
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finsupp.Defs

/-!
# Finite supports for the frame rank

The index action fixes every point below a fixed point. A frame below an
anchor is determined by the anchor and a finite support, which can itself be
recovered from the pair. Comparing the greatest support indices then gives the
two successive comparison clauses in the disjointifying rank. All ranks here
are for the group acting on the structure, including its restricted actions
on the different sorts.
-/

namespace KnightModel.RankTwo

variable {G I F C : Type*} [Group G]

/-- An automorphism fixing an index fixes its entire principal lower set. -/
def FixesBelow (G I : Type*) [Group G] [MulAction G I] [LE I] : Prop :=
  ∀ (g : G) (i j : I), i ≤ j → g • j = j → g • i = i

/-- This property follows from the actual Knight functions in the index sort. -/
theorem fixesBelow_of_knight {I Ω : Type} [Blueprint Ω] [KnightModel I Ω] [MulAction G I]
    (comm : ∀ (g : G) (n : Ω) (x : I),
      g • KnightModel.fn n x = KnightModel.fn n (g • x)) : FixesBelow G I := by
  intro g i j hij hj
  obtain ⟨n, hn⟩ := KnightModel.capture (Ω := Ω) i j hij
  rw [← hn, comm, hj]

/-- The point and its finite index support have the same pointwise stabilizer. -/
def FiniteSupportFor (G I : Type*) [Group G] [MulAction G I] {C : Type*} [MulAction G C]
    (p : C) (s : Finset I) : Prop :=
  ∀ g : G, g • p = p ↔ ∀ i ∈ s, g • i = i

/-- Recoverability of the support and sufficiency of the support, relative to an anchor. -/
def FrameSupport (G I : Type*) [Group G] [MulAction G I] {F : Type*} [MulAction G F]
    (u v : F) (s : Finset I) : Prop :=
  ∀ g : G, g • v = v → (g • u = u ↔ ∀ i ∈ s, g • i = i)

/-- A recovered transition code with finite index support provides frame support. -/
theorem frameSupport_of_code [MulAction G I] [MulAction G F] [MulAction G C]
    {u v : F} {p : C} {s : Finset I} (hp : FiniteSupportFor G I p s)
    (recover : ∀ g : G, g • v = v → g • u = u → g • p = p)
    (determine : ∀ g : G, g • v = v → g • p = p → g • u = u) : FrameSupport G I u v s :=
  fun g hv => ⟨fun hu => (hp g).mp (recover g hv hu),
    fun hs => determine g hv ((hp g).mpr hs)⟩

section Ordered

variable [LinearOrder I] [MulAction G I] [MulAction G F]

/-- In the nonempty case a single greatest index suffices. -/
theorem frameSupport_iff_fix_max (below : FixesBelow G I) {u v : F} {s : Finset I}
    (hs : FrameSupport G I u v s) (hne : s.Nonempty) (g : G) (hv : g • v = v) :
    g • u = u ↔ g • s.max' hne = s.max' hne :=
  ⟨fun hu => (hs g hv).mp hu _ (s.max'_mem hne),
    fun hm => (hs g hv).mpr fun i hi => below g i _ (s.le_max' i hi) hm⟩

private theorem comparable_supports (s t : Finset I) :
    (∀ i ∈ s, ∃ j ∈ t, i ≤ j) ∨ (∀ j ∈ t, ∃ i ∈ s, j ≤ i) := by
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · rcases le_total (s.max' hs) (t.max' ht) with h | h
      · exact Or.inl fun i hi => ⟨_, t.max'_mem ht, (s.le_max' i hi).trans h⟩
      · exact Or.inr fun j hj => ⟨_, s.max'_mem hs, (t.le_max' j hj).trans h⟩
    · exact Or.inr fun j hj => (ht ⟨j, hj⟩).elim
  · exact Or.inl fun i hi => (hs ⟨i, hi⟩).elim

private theorem fix_smaller_support (below : FixesBelow G I) {s t : Finset I}
    (h : ∀ i ∈ s, ∃ j ∈ t, i ≤ j) (g : G) (ht : ∀ j ∈ t, g • j = j) :
    ∀ i ∈ s, g • i = i := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := h i hi
  exact below g i j hij (ht j hj)

/-- Singleton rank in any sort with recoverable finite Knight support. -/
theorem rankLE_one_of_support (below : FixesBelow G I)
    (support : ∀ x : F, ∃ s, FiniteSupportFor G I x s) (x : F) : RankLE G 1 [] x := by
  refine Or.inr fun y _ => ?_
  obtain ⟨s, hs⟩ := support x
  obtain ⟨t, ht⟩ := support y
  rcases comparable_supports s t with h | h
  · exact Or.inl fun g hg => (hs g).mpr
      (fix_smaller_support below h g ((ht g).mp (hg y List.mem_cons_self)))
  · exact Or.inr fun g hg => (ht g).mpr
      (fix_smaller_support below h g ((hs g).mp (hg x List.mem_cons_self)))

/-- The index sort has singleton rank at most one. -/
theorem index_rankLE_one (below : FixesBelow G I) (x : I) : RankLE G 1 [] x := by
  refine Or.inr fun y _ => ?_
  rcases le_total x y with h | h
  · exact Or.inl fun g hg => below g x y h (hg y List.mem_cons_self)
  · exact Or.inr fun g hg => below g y x h (hg x List.mem_cons_self)

variable {r : F → F → Prop}

/-- The rank of a lower frame over a fixed upper frame is at most one. -/
theorem frame_rankLE_one_of_le (below : FixesBelow G I)
    (pres : ∀ (g : G) {u v : F}, r u v → r (g • u) (g • v))
    (support : ∀ u v, r u v → ∃ s, FrameSupport G I u v s)
    {u v : F} (huv : r u v) : RankLE G 1 [v] u := by
  refine Or.inr ?_
  rintro _ ⟨g, hg, rfl⟩
  have hgv := hg v List.mem_cons_self
  have hy : r (g • u) v := hgv ▸ pres g huv
  obtain ⟨s, hs⟩ := support u v huv
  obtain ⟨t, ht⟩ := support (g • u) v hy
  rcases comparable_supports s t with h | h
  · apply Or.inl
    intro k hk
    have hv := hk v (List.mem_cons_of_mem _ List.mem_cons_self)
    exact (hs k hv).mpr
      (fix_smaller_support below h k ((ht k hv).mp (hk _ List.mem_cons_self)))
  · apply Or.inr
    intro k hk
    have hv := hk v (List.mem_cons_of_mem _ List.mem_cons_self)
    exact (ht k hv).mpr
      (fix_smaller_support below h k ((hs k hv).mp (hk _ List.mem_cons_self)))

/-- Endpoint comparability supplies the outer comparison clause for every frame. -/
theorem frame_rankLE_two (below : FixesBelow G I) (total : ∀ u v, r u v ∨ r v u)
    (pres : ∀ (g : G) {u v : F}, r u v → r (g • u) (g • v))
    (support : ∀ u v, r u v → ∃ s, FrameSupport G I u v s)
    (u : F) : RankLE G 2 [] u := by
  refine Or.inr fun v _ => ?_
  exact (total u v).imp (frame_rankLE_one_of_le below pres support)
    (frame_rankLE_one_of_le below pres support)

end Ordered

section Vectors

variable [LinearOrder I] [MulAction G I] {A : Type*} [Zero A] [MulAction G (I →₀ A)]

/-- Preserving the coefficients under an increasing permutation of the Knight
indices makes the ordinary support of a finitely supported vector recoverable. -/
theorem finsupp_finiteSupportFor (below : FixesBelow G I)
    (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (v : I →₀ A) : FiniteSupportFor G I v v.support := by
  intro g
  constructor
  · intro hv i hi
    have hs (j : I) : g • j ∈ v.support ↔ j ∈ v.support := by
      simp only [Finsupp.mem_support_iff]
      rw [← coeff g v j, hv]
    let m := v.support.max' ⟨i, hi⟩
    have hm : m ∈ v.support := v.support.max'_mem _
    have hm' : g⁻¹ • m ∈ v.support := (hs (g⁻¹ • m)).mp (by simpa using hm)
    have lower : m ≤ g • m := by
      simpa using mono g (v.support.le_max' _ hm')
    have fixed : g • m = m := le_antisymm (v.support.le_max' _ ((hs m).mpr hm)) lower
    exact below g i m (v.support.le_max' i hi) fixed
  · intro hs
    ext i
    have hcoeff : (g • v) i = v (g⁻¹ • i) := by simpa using coeff g v (g⁻¹ • i)
    rw [hcoeff]
    by_cases hi : i ∈ v.support
    · have hf : g⁻¹ • i = i := by
        simpa using (congrArg (fun j : I => g⁻¹ • j) (hs i hi)).symm
      rw [hf]
    · have hpre : g⁻¹ • i ∉ v.support := by
        intro h
        apply hi
        have heq : i = g⁻¹ • i := by simpa using hs (g⁻¹ • i) h
        simpa only [← heq] using h
      rw [Finsupp.notMem_support_iff.mp hpre, Finsupp.notMem_support_iff.mp hi]

/-- The vector sort therefore has singleton rank at most one. -/
theorem vector_rankLE_one (below : FixesBelow G I)
    (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (v : I →₀ A) : RankLE G 1 [] v :=
  rankLE_one_of_support below (fun x => ⟨_, finsupp_finiteSupportFor below mono coeff x⟩) v

end Vectors

section CanonicalParameters

variable [LinearOrder I] [MulAction G I] [MulAction G F] {A : Type*} [Zero A]
    [MulAction G (I →₀ A)] {r : F → F → Prop}

/-- The parameter statement needed from the choice of a canonical program:
over the upper frame, the lower frame and its parameter tuple fix one another.
The scheme index is a named natural number and needs no support. -/
def HasCanonicalParameters (G I A : Type*) [Group G] [Zero A] [MulAction G (I →₀ A)]
    {F : Type*} [MulAction G F] (r : F → F → Prop) : Prop :=
  ∀ u v, r u v → ∃ (n : ℕ) (p : Fin n → I →₀ A),
    ∀ g : G, g • v = v → (g • u = u ↔ ∀ j, g • p j = p j)

/-- To obtain canonical parameters, it suffices that each nonempty fiber of one
transition scheme has a member fixed by every group element preserving that
fiber setwise. No choice of scheme across different pairs is needed. -/
theorem hasCanonicalParameters_of_transition_fibers {K : Type*} (arity : K → ℕ)
    (R : (k : K) → F → F → (Fin (arity k) → I →₀ A) → Prop)
    (covers : ∀ u v, r u v → ∃ k p, R k u v p)
    (functional : ∀ k u u' v p, R k u v p → R k u' v p → u = u')
    (invariant : ∀ (g : G) k u v p,
      R k u v p ↔ R k (g • u) (g • v) (fun j => g • p j))
    (choice : ∀ k u v, (∃ q, R k u v q) → ∃ p, R k u v p ∧
      ∀ g : G, (∀ q, R k u v q ↔ R k u v (fun j => g • q j)) →
        ∀ j, g • p j = p j) : HasCanonicalParameters G I A r := by
  intro u v huv
  obtain ⟨k, q, hq⟩ := covers u v huv
  obtain ⟨p, hp, fixed⟩ := choice k u v ⟨q, hq⟩
  refine ⟨arity k, p, fun g hv => ⟨?_, ?_⟩⟩
  · intro hu
    exact fixed g fun t => by simpa only [hu, hv] using invariant g k u v t
  · intro hfix
    have he : (fun j => g • p j) = p := funext hfix
    have hmap := (invariant g k u v p).mp hp
    rw [hv, he] at hmap
    exact functional k _ _ v p hmap hp

/-- Take the union of the ordinary vector supports of the chosen parameters. -/
theorem exists_frameSupport_of_canonical_parameters (below : FixesBelow G I)
    (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (params : HasCanonicalParameters G I A r) {u v : F} (h : r u v) :
    ∃ s, FrameSupport G I u v s := by
  classical
  obtain ⟨n, p, hp⟩ := params u v h
  refine ⟨Finset.univ.biUnion (fun j : Fin n => (p j).support), fun g hv => (hp g hv).trans ?_⟩
  constructor
  · intro hfixed i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    exact (finsupp_finiteSupportFor below mono coeff (p j) g).mp (hfixed j) i hj
  · intro hfixed j
    exact (finsupp_finiteSupportFor below mono coeff (p j) g).mpr fun i hi =>
      hfixed i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩)

/-- The rank bound on the actual disjoint union of the index, vector and frame
sorts, for any group of sort-preserving automorphisms satisfying the indicated
transition-parameter property. The ambient action includes all three sorts at
every stage of the rank definition. -/
theorem threeSort_rankLE_two (below : FixesBelow G I)
    (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (total : ∀ u v, r u v ∨ r v u)
    (pres : ∀ (g : G) {u v : F}, r u v → r (g • u) (g • v))
    (params : HasCanonicalParameters G I A r) (x : I ⊕ ((I →₀ A) ⊕ F)) :
    RankLE G 2 [] x := by
  cases x with
  | inl i =>
    exact rankLE_of_equivariant_embedding Sum.inl (fun _ _ h => Sum.inl.inj h)
      (fun _ _ => rfl) (index_rankLE_one below i).succ
  | inr y =>
    cases y with
    | inl v =>
      exact rankLE_of_equivariant_embedding (fun q => Sum.inr (Sum.inl q))
        (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)) (fun _ _ => rfl)
        (vector_rankLE_one below mono coeff v).succ
    | inr u =>
      exact rankLE_of_equivariant_embedding (fun q => Sum.inr (Sum.inr q))
        (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)) (fun _ _ => rfl)
        (frame_rankLE_two below total pres
          (fun _ _ h => exists_frameSupport_of_canonical_parameters below mono coeff params h) u)

end CanonicalParameters

end KnightModel.RankTwo
