import KnightModel.RankTwo.RestrictionSkeleton

/-! # Simultaneous thinning of finitely many coordinate relations -/

namespace KnightModel.RankTwo.Restriction

open Set Cardinal

/-- Any countable coloring of an uncountable subset has an uncountable fiber. -/
theorem exists_uncountable_color {X Y : Type} [Countable Y] (S : Set X)
    (hS : ¬ S.Countable) (f : X → Y) : ∃ y, ¬ {x ∈ S | f x = y}.Countable := by
  by_contra! all
  apply hS
  exact (countable_iUnion all).mono (by
    intro x hx
    exact mem_iUnion.mpr ⟨f x, (show x ∈ {z ∈ S | f z = f x} from ⟨hx, rfl⟩)⟩)

/-- After thinning a family of parameterized points, either their value is
constant or the inverse image of every countable set is countable. -/
theorem thin_constant_or_countable_preimages {X Y : Type} (S : Set X)
    (hS : ¬ S.Countable) (f : X → Y) :
    ∃ T ⊆ S, ¬ T.Countable ∧
      ((∃ y, ∀ x ∈ T, f x = y) ∨ ∀ Q : Set Y, Q.Countable → {x ∈ T | f x ∈ Q}.Countable) := by
  classical
  by_cases h : ∃ y, ¬ {x ∈ S | f x = y}.Countable
  · obtain ⟨y, hy⟩ := h
    exact ⟨_, fun _ hx => hx.1, hy, .inl ⟨y, fun _ hx => hx.2⟩⟩
  · push Not at h
    refine ⟨S, fun _ hx => hx, hS, .inr fun Q hQ => ?_⟩
    exact (hQ.biUnion fun q _ => h q).mono (by
      intro x hx
      exact mem_iUnion.mpr ⟨f x, mem_iUnion.mpr ⟨hx.2, (show x ∈ {z ∈ S | f z = f x} from ⟨hx.1, rfl⟩)⟩⟩)

private theorem thin_finitely {X : Type} {n : ℕ} (S : Set X) (hS : ¬ S.Countable)
    (r : Fin n → X → X → Prop)
    (thin : ∀ j (s : Set X), s ⊆ S → ¬ s.Countable → ∃ t ⊆ s, ¬ t.Countable ∧
      ∀ x ∈ t, {y ∈ t | ¬ r j x y}.Countable) :
    ∃ t ⊆ S, ¬ t.Countable ∧ ∀ j x, x ∈ t → {y ∈ t | ¬ r j x y}.Countable := by
  induction n with
  | zero => exact ⟨S, fun _ hs => hs, hS, fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨s,sub,hs,tail⟩ := ih (fun j => r j.succ) (fun j => thin j.succ)
    obtain ⟨t,ts,ht,head⟩ := thin 0 s sub hs
    refine ⟨t, ts.trans sub, ht, fun j => ?_⟩
    exact Fin.cases head (fun k x hx =>
      (tail k x (ts hx)).mono (by
        intro y hy
        exact (show y ∈ {z ∈ s | ¬ r k.succ x z} from ⟨ts hy.1, hy.2⟩))) j

/-- An uncountable family contains an omega-one sequence avoiding all the bad
successors of each of its predecessors when these exceptional sets are countable. -/
theorem avoid_countable_successors {X : Type} (S : Set X) (hS : ¬ S.Countable)
    (bad : X → Set X) (small : ∀ x ∈ S, (bad x).Countable) :
    ∃ e : OmegaOne ↪ X, (∀ i, e i ∈ S) ∧ ∀ i j, i < j → e j ∉ bad (e i) := by
  classical
  have next (i : OmegaOne) (old : Iio i → S) :
      ∃ z : S, ∀ j, z.val ≠ (old j).val ∧ z.val ∉ bad (old j).val := by
    haveI : Countable (Iio i) := le_aleph0_iff_set_countable.mp <| lt_aleph_one_iff.mp
      (by simpa using mk_Iio_lt i (by simp))
    let used : Set X := ⋃ j, (insert (old j).val (bad (old j).val))
    have hu : used.Countable := countable_iUnion (fun j => (small _ (old j).property).insert _)
    obtain ⟨z, hz, free⟩ := not_subset.mp (fun h => hS (hu.mono h))
    exact ⟨⟨z,hz⟩, fun j => by
      have h : z ∉ insert (old j).val (bad (old j).val) := fun hz => free (mem_iUnion.mpr ⟨j,hz⟩)
      simpa only [mem_insert_iff, not_or] using h⟩
  let f : OmegaOne → S := wellFounded_lt.fix fun i ih => (next i (fun j => ih j.val j.property)).choose
  have spec (i j : OmegaOne) (h : i < j) : (f j).val ≠ (f i).val ∧ (f j).val ∉ bad (f i).val := by
    have eqn : f j = (next j (fun p => f p.val)).choose := by
      unfold f
      rw [WellFounded.fix_eq]
    rw [eqn]
    exact (next j (fun p => f p.val)).choose_spec ⟨i,h⟩
  refine ⟨⟨fun i => (f i).val, fun {i j} h => ?_⟩, fun i => (f i).property,
    fun i j hij => (spec i j hij).2⟩
  rcases lt_trichotomy i j with less | eqn | gt
  · exact False.elim ((spec i j less).1 h.symm)
  · exact eqn
  · exact False.elim ((spec j i gt).1 h)

/-- A finite list of coordinate thinnings can be performed simultaneously.
The final transfinite recursion avoids a countable union of forbidden sets. -/
theorem simultaneous_tuple_thinning {X : Type} {n : ℕ} (S : Set X) (hS : ¬ S.Countable)
    (r : Fin n → X → X → Prop)
    (thin : ∀ j (s : Set X), s ⊆ S → ¬ s.Countable → ∃ t ⊆ s, ¬ t.Countable ∧
      ∀ x ∈ t, {y ∈ t | ¬ r j x y}.Countable) :
    ∃ e : OmegaOne ↪ X, (∀ i, e i ∈ S) ∧ ∀ i k, i < k → ∀ j, r j (e i) (e k) := by
  obtain ⟨t, ts, ht, small⟩ := thin_finitely S hS r thin
  let bad (x : X) := ⋃ j, {y ∈ t | ¬ r j x y}
  obtain ⟨e, he, avoid⟩ := avoid_countable_successors t ht bad fun x hx =>
    countable_iUnion fun j => small j x hx
  exact ⟨e, fun i => ts (he i), fun i k hik j => Classical.byContradiction fun no =>
    avoid i k hik (mem_iUnion.mpr ⟨j, he k, no⟩)⟩

end KnightModel.RankTwo.Restriction
