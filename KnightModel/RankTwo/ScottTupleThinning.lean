import KnightModel.RankTwo.RestrictionTupleThinning
import KnightModel.RankTwo.ScottGlobalDiagrams

/-! # Simultaneous rank-zero comparison for finite Scott tuples -/

namespace KnightModel.RankTwo.Scott

open Set Cardinal Restriction

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

local notation "F" => C.system D E sat

/-- In one coordinate, thin to a constant source label and either to a repeated
value or to a family with countable preimages of countable lower cones. -/
theorem thin_low_coordinate {X : Type} {k : ℕ} (base : Tuple N k) (f : X → N)
    (low : ∀ i, f i ∈ lowFiber F 1 base) (s : Set X) (hs : ¬ s.Countable) :
    ∃ t ⊆ s, ¬ t.Countable ∧ ∀ x ∈ t, {y ∈ t | f x ∉ lowFiber F 0 (push (f y) base)}.Countable := by
  classical
  let labels (i : X) : M × Tuple M k := ⟨(low i).choose, (low i).choose_spec.choose⟩
  have member (i : X) : ModelRankLE D 1 (List.ofFn (labels i).2) (labels i).1 ∧
      f i ∈ orbitFiber F (labels i).2 (labels i).1 base := (low i).choose_spec.choose_spec
  haveI : Countable M := Function.Surjective.countable (f := C.enum) C.onto
  obtain ⟨q, hq⟩ := exists_uncountable_color s hs labels
  let U := {i ∈ s | labels i = q}
  have good (i : X) (hi : i ∈ U) : ModelRankLE D 1 (List.ofFn q.2) q.1 ∧
      f i ∈ orbitFiber F q.2 q.1 base := hi.2 ▸ member i
  obtain ⟨t, tu, ht, constant | count⟩ := thin_constant_or_countable_preimages U hq f
  · obtain ⟨z, hz⟩ := constant
    refine ⟨t, fun i hi => (tu hi).1, ht, fun x hx => ?_⟩
    apply (countable_empty : (∅ : Set X).Countable).mono
    intro y hy
    exact (hy.2 ((hz x hx).symm ▸ (hz y hy.1).symm ▸ mem_lowFiber_self C sat z base)).elim
  · have ne := nonempty_iff_ne_empty.mpr (show t ≠ ∅ from fun h => ht (h ▸ countable_empty))
    obtain ⟨x₀, hx₀⟩ := ne
    have good0 := good x₀ (tu hx₀)
    have countCone (y : N) : (lowFiber F 0 (push y base)).Countable :=
      le_aleph0_iff_set_countable.mp (by simpa using lowFiber_cardinal F C 0 (push y base))
    rcases orbitFiber_dichotomy F C q.2 q.1 base good0.1 ⟨_, good0.2⟩ with ⟨d, cover⟩ | pair
    · exact (ht ((count _ (countCone d)).mono (by
        intro i hi
        exact ⟨hi, cover (good i (tu hi)).2⟩))).elim
    · refine ⟨t, fun i hi => (tu hi).1, ht, fun x hx => (count _ (countCone (f x))).mono ?_⟩
      intro y hy
      have comp := pair _ (good x (tu hx)).2 _ (good y (tu hy.1)).2
      exact ⟨hy.1, comp.resolve_right hy.2⟩

/-- An uncountable family of tuples with individually rank-one entries contains
an omega-one sequence of distinct family indices increasing in every coordinate
for definable dependence over the given base. -/
theorem low_tuple_comparison_chain {X : Type} {k n : ℕ} (base : Tuple N k)
    (v : X → Tuple N n) (low : ∀ i j, v i j ∈ lowFiber F 1 base)
    (s : Set X) (hs : ¬ s.Countable) :
    ∃ e : OmegaOne ↪ X, (∀ i, e i ∈ s) ∧ ∀ i l, i ≤ l → ∀ j,
      v (e i) j ∈ lowFiber F 0 (push (v (e l) j) base) := by
  obtain ⟨e, he, chain⟩ := simultaneous_tuple_thinning s hs
    (fun j a b => v a j ∈ lowFiber F 0 (push (v b j) base)) (fun j t _ ht =>
      thin_low_coordinate C sat base (fun x => v x j) (fun x => low x j) t ht)
  refine ⟨e, he, fun i l il j => ?_⟩
  rcases il.eq_or_lt with rfl | il
  · exact mem_lowFiber_self C sat _ _
  · exact chain i l il j

end KnightModel.RankTwo.Scott
