import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal bounds from comparable fibers

If every pair is covered in one direction by fibers of size at most an infinite κ,
the ambient set has size at most κ⁺. This applies even when the covering relation
is neither antisymmetric nor transitive.
-/

namespace KnightModel.RankTwo

open Cardinal Set

/-- A family of small sets which covers every pair in one direction bounds the
cardinality of the underlying type by the successor cardinal. -/
theorem cardinal_le_succ_of_pair_cover {X : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (lower : X → Set X) (small : ∀ x, #(lower x) ≤ κ)
    (compare : ∀ x y, x ∈ lower y ∨ y ∈ lower x) : #X ≤ Order.succ κ := by
  by_contra! h
  obtain ⟨S, hS⟩ := le_mk_iff_exists_set.mp h.le
  have cover : (⋃ x : S, lower x.val) = Set.univ := by
    apply eq_univ_of_forall
    intro y
    by_contra hy
    have contained : S ⊆ lower y := by
      intro x hx
      exact (compare x y).resolve_right (fun hxy => hy (mem_iUnion.mpr ⟨⟨x, hx⟩, hxy⟩))
    exact (Order.lt_succ κ).not_ge (hS ▸ (mk_le_mk_of_subset contained).trans (small y))
  have bound : #X ≤ Order.succ κ := calc
    #X = #(⋃ x : S, lower x.val) := by rw [cover, mk_univ]
    _ ≤ Cardinal.sum (fun x : S => #(lower x.val)) := mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : S => Order.succ κ) :=
      Cardinal.sum_le_sum _ _ fun x => (small x.val).trans (Order.le_succ κ)
    _ = #S * Order.succ κ := sum_const' _ _
    _ = Order.succ κ := by rw [hS, mul_eq_self (hκ.trans (Order.le_succ κ))]
  exact h.not_ge bound

/-- Frame transitions are indexed by countably many schemes and finite lists of
vector parameters. Multiple codes may denote the same transition. -/
theorem cardinal_frames_le_aleph_two {F V : Type} (hV : #V ≤ ℵ₁)
    (lower : F → Set F) (compare : ∀ u v, u ∈ lower v ∨ v ∈ lower u)
    (encode : ∀ v, Nonempty (lower v ↪ ℕ × List V)) : #F ≤ aleph 2 := by
  have small (v : F) : #(lower v) ≤ ℵ₁ := calc
    #(lower v) ≤ #(ℕ × List V) := (encode v).elim fun f => mk_le_of_injective f.injective
    _ = ℵ₀ * #(List V) := by simp [mk_prod]
    _ ≤ ℵ₁ * ℵ₁ := mul_le_mul' (aleph0_le_aleph 1)
      ((mk_list_le_max V).trans (max_le (aleph0_le_aleph 1) hV))
    _ = ℵ₁ := mul_eq_self (aleph0_le_aleph 1)
  simpa only [succ_aleph, one_add_one_eq_two] using
    cardinal_le_succ_of_pair_cover (aleph0_le_aleph 1) lower small compare

end KnightModel.RankTwo
