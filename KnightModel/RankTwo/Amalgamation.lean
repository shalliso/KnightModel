import KnightModel.RankTwo.Cardinality
import Mathlib.Order.Zorn

/-! # The countable compatibility bound for twisted extensions

A finite pair label records which of the orbital functions at the first
marked point equal which orbital functions at the second. This works even
when a prospective amalgam identifies the two marked points.
-/

namespace KnightModel.RankTwo.Amalgamation

open Set Cardinal

variable {P L X : Type*}

/-- The table read from the label of a pair of marked points. -/
def Records (table : L → P → P → Prop) (l : L) (s t : Equiv.Perm P) : Prop :=
  ∀ i j, table l i j ↔ s i = t j

/-- Once the left twist is fixed, the pair label determines the right twist pointwise. -/
theorem records_unique {table : L → P → P → Prop} {l : L} {s t u : Equiv.Perm P}
    (ht : Records table l s t) (hu : Records table l s u) : t = u := by
  ext j
  let i := s.symm (t j)
  have hi : s i = t j := s.apply_symm_apply _
  exact hi.symm.trans ((hu i j).mp ((ht i j).mpr hi))

/-- The possible neighbors of one twist inject into the countable label set. -/
theorem countable_compatible [Countable L] (twist : X ↪ Equiv.Perm P)
    (compat : X → X → Prop) (table : L → P → P → Prop)
    (labels : ∀ a b, compat a b → ∃ l, Records table l (twist a) (twist b)) (a : X) :
    {b | compat a b}.Countable := by
  classical
  let label (b : {t | compat a t}) := (labels a b.val b.property).choose
  apply Function.Injective.countable (f := label)
  intro b c he
  have hb := (labels a b.val b.property).choose_spec
  have hc := (labels a c.val c.property).choose_spec
  change Records table (label b) _ _ at hb
  change Records table (label c) _ _ at hc
  rw [he] at hb
  exact Subtype.ext (twist.injective (records_unique hb hc))

/-- In any uncountable family with symmetric compatibility and countable
neighborhoods, some pairwise incompatible subfamily has full cardinality.
The argument works without a regularity assumption on that cardinal. -/
theorem exists_full_incompatible {X : Type u} (compat : X → X → Prop)
    (sym : ∀ x y, compat x y → compat y x)
    (small : ∀ x, {y | compat x y}.Countable) (unc : ℵ₀ < #X) :
    ∃ S : Set X, #S = #X ∧ S.Pairwise (fun x y => ¬ compat x y) := by
  classical
  let good := {S : Set X | S.Pairwise (fun x y => ¬ compat x y)}
  obtain ⟨S,hS⟩ := zorn_subset good (by
    intro c hc chain
    refine ⟨⋃₀ c, ?_,fun s hs => subset_sUnion_of_mem hs⟩
    intro x hx y hy ne
    obtain ⟨s,hs,hxs⟩ := mem_sUnion.mp hx
    obtain ⟨t,ht,hyt⟩ := mem_sUnion.mp hy
    rcases chain.directedOn s hs t ht with ⟨u,hu,hsu,htu⟩
    exact hc hu (hsu hxs) (htu hyt) ne)
  let ball (x : X) := insert x {y | compat x y}
  have cover : (⋃ a : S, ball a.val) = Set.univ := by
    apply eq_univ_of_forall
    intro y
    by_contra hn
    have missing (a : S) : y ∉ ball a.val := fun h => hn (mem_iUnion.mpr ⟨a,h⟩)
    have hy : y ∉ S := fun hy => missing ⟨y,hy⟩ (mem_insert _ _)
    have enlarged : insert y S ∈ good := by
      refine hS.prop.insert (fun x hx _ => ?_)
      have h : ¬ compat x y := fun h => missing ⟨x,hx⟩ (mem_insert_of_mem _ h)
      exact ⟨fun q => h (sym _ _ q),h⟩
    exact hy ((hS.le_of_ge enlarged (subset_insert _ _)) (mem_insert _ _))
  have bound : #X ≤ max #S ℵ₀ := calc
    #X = #(⋃ a : S, ball a.val) := by rw [cover,mk_univ]
    _ ≤ Cardinal.sum (fun a : S => #(ball a.val)) := mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : S => ℵ₀) := Cardinal.sum_le_sum _ _ (fun a =>
      mk_le_aleph0_iff.mpr ((small a.val).insert a.val))
    _ = #S * ℵ₀ := sum_const' _ _
    _ ≤ max #S ℵ₀ := mul_le_max_of_aleph0_le_right le_rfl
  exact ⟨S,le_antisymm (mk_set_le _) ((le_max_iff.mp bound).resolve_right unc.not_ge),hS.prop⟩

/-- In particular an action image of size continuum yields continuum many
pairwise nonamalgamable twists. The comparison data may vary with the amalgam. -/
theorem continuum_incompatible [Countable L] (twist : X ↪ Equiv.Perm P)
    (compat : X → X → Prop) (table : L → P → P → Prop)
    (labels : ∀ a b, compat a b → ∃ l, Records table l (twist a) (twist b))
    (sym : ∀ x y, compat x y → compat y x) (hX : #X = 2 ^ ℵ₀) :
    ∃ S : Set X, #S = 2 ^ ℵ₀ ∧ S.Pairwise (fun x y => ¬ compat x y) := by
  obtain ⟨S,hS,hi⟩ := exists_full_incompatible compat sym
    (countable_compatible twist compat table labels) (hX ▸ cantor ℵ₀)
  exact ⟨S,hS.trans hX,hi⟩

end KnightModel.RankTwo.Amalgamation
