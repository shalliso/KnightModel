import KnightModel.RankTwo.RankFrame
import Mathlib.Order.Hom.Set
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Recoverable finite supports in a successor frame sort

An ordered finite set has no nonidentity order automorphisms. Consequently a
vector determines every index in its support, even when its largest index
alone can move the smaller ones. Comparing the maximal coordinate of two
finite tuples then extends the relative support property from points to tuples.
-/

namespace KnightModel.Transfinite

open RankTwo

variable {G I X F A : Type*} [Group G] [LinearOrder I] [MulAction G I]

/-- Fixing a vector fixes exactly the indicated finite set of indices. -/
theorem vectorSupport [Zero A] [MulAction G (I →₀ A)]
    (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (v : I →₀ A) : FiniteSupportFor G I v v.support := by
  classical
  intro g
  constructor
  · intro hv
    have hs (i : I) : g • i ∈ v.support ↔ i ∈ v.support := by
      simp only [Finsupp.mem_support_iff]
      rw [← coeff g v i, hv]
    let e : v.support ≃o v.support := {
      toFun := fun i => ⟨g • i.val, (hs i.val).mpr i.property⟩
      invFun := fun i => ⟨g⁻¹ • i.val, (hs _).mp (by simp)⟩
      left_inv := fun i => Subtype.ext (inv_smul_smul g i.val)
      right_inv := fun i => Subtype.ext (smul_inv_smul g i.val)
      map_rel_iff' := by
        intro i j
        change (g • i.val ≤ g • j.val) ↔ i.val ≤ j.val
        exact ⟨fun h => by simpa using mono g⁻¹ h, fun h => mono g h⟩ }
    have he := Subsingleton.elim e (OrderIso.refl _)
    exact fun i hi => congrArg (fun f : v.support ≃o v.support => (f ⟨i, hi⟩).val) he
  · intro hs
    ext i
    have hc : (g • v) i = v (g⁻¹ • i) := by simpa using coeff g v (g⁻¹ • i)
    rw [hc]
    by_cases hi : i ∈ v.support
    · have he := congrArg (fun j : I => g⁻¹ • j) (hs i hi)
      simp only [inv_smul_smul] at he
      exact congrArg v he.symm
    · have hn : g⁻¹ • i ∉ v.support := by
        intro h
        have he : i = g⁻¹ • i := by simpa using hs _ h
        exact hi (he ▸ h)
      rw [Finsupp.notMem_support_iff.mp hi, Finsupp.notMem_support_iff.mp hn]

/-- The union of the supports of a canonical transition parameter is recovered
from the two frames, and determines the lower frame relative to the upper one. -/
theorem canonicalFrameSupport [Zero A] [MulAction G (I →₀ A)] [MulAction G F]
    {r : F → F → Prop} (mono : ∀ g : G, Monotone (fun i : I => g • i))
    (coeff : ∀ (g : G) (v : I →₀ A) (i : I), (g • v) (g • i) = v i)
    (canon : HasCanonicalParameters G I A r) {u v : F} (h : r u v) :
    ∃ s, FrameSupport G I u v s := by
  classical
  obtain ⟨n, p, hp⟩ := canon u v h
  refine ⟨Finset.univ.biUnion (fun j : Fin n => (p j).support), fun g hg => (hp g hg).trans ?_⟩
  constructor
  · intro hv i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    exact (vectorSupport mono coeff (p j) g).mp (hv j) i hj
  · intro hv j
    exact (vectorSupport mono coeff (p j) g).mpr fun i hi =>
      hv i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩)

omit [LinearOrder I] in
/-- A finite tuple is determined by the combined relative supports of its entries. -/
theorem unionTupleSupport [MulAction G X] {n : ℕ} (x : Fin n → X) (H : Subgroup G)
    (support : ∀ j, ∃ s : Finset I, ∀ g ∈ H, g • x j = x j ↔ ∀ i ∈ s, g • i = i) :
    ∃ s : Finset I, ∀ g ∈ H, g • x = x ↔ ∀ i ∈ s, g • i = i := by
  classical
  choose s hs using support
  refine ⟨Finset.univ.biUnion s, fun g hg => ?_⟩
  constructor
  · intro hx i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    exact (hs j g hg).mp (congrFun hx j) i hj
  · intro h
    exact funext fun j => (hs j g hg).mpr fun i hi =>
      h i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩)

private theorem finite_anchor (r : X → X → Prop) (total : ∀ a b, r a b ∨ r b a)
    (trans : ∀ {a b c}, r a b → r b c → r a c)
    (s : Finset X) (ne : s.Nonempty) : ∃ b ∈ s, ∀ a ∈ s, r a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ne
  | @insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with he | nonempty
    · subst s
      simpa using (total a a).elim id id
    obtain ⟨b, hb, bound⟩ := ih nonempty
    rcases total a b with hab | hba
    · exact ⟨b, Finset.mem_insert_of_mem hb, fun x hx =>
        (Finset.mem_insert.mp hx).elim (fun h => h ▸ hab) (bound x)⟩
    · exact ⟨a, Finset.mem_insert_self _ _, fun x hx =>
        (Finset.mem_insert.mp hx).elim (fun h => by subst x; exact (total a a).elim id id)
          (fun hx => trans (bound x hx) hba)⟩

omit [LinearOrder I] in
/-- One of two arbitrary equal-arity tuples is coded by finitely many old
indices relative to the other. An endpoint of maximal height in their union
belongs to one of the tuples, so fixing that tuple fixes this anchor. -/
theorem compareTupleSupports [MulAction G X] (r : X → X → Prop)
    (total : ∀ a b, r a b ∨ r b a) (trans : ∀ {a b c}, r a b → r b c → r a c)
    (support : ∀ a b, r a b → ∃ s, FrameSupport G I a b s) {n : ℕ} (x y : Fin n → X) :
    (∃ s : Finset I, ∀ g : G, g • y = y → (g • x = x ↔ ∀ i ∈ s, g • i = i)) ∨
    (∃ s : Finset I, ∀ g : G, g • x = x → (g • y = y ↔ ∀ i ∈ s, g • i = i)) := by
  classical
  cases n with
  | zero => exact Or.inl ⟨∅, fun _ _ => iff_of_true (funext fun j => j.elim0) (by simp)⟩
  | succ n =>
    let a := Finset.univ.image x
    let b := Finset.univ.image y
    obtain ⟨u, hu, greatest⟩ := finite_anchor r total trans (a ∪ b)
      ⟨x 0, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)⟩
    have anchored (t z : Fin (n+1) → X) (j : Fin (n+1)) (hj : z j = u)
        (bound : ∀ k, r (t k) u) :
        ∃ s : Finset I, ∀ g : G, g • z = z → (g • t = t ↔ ∀ i ∈ s, g • i = i) := by
      apply unionTupleSupport t (MulAction.stabilizer G z)
      intro k
      obtain ⟨v, hv⟩ := support _ _ (bound k)
      refine ⟨v, fun g hg => hv g ?_⟩
      have h := congrFun (show g • z = z from hg) j
      simpa only [Pi.smul_apply, hj] using h
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hu
      exact Or.inr (anchored y x j hj fun k => greatest _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)))
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hu
      exact Or.inl (anchored x y j hj fun k => greatest _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)))

end KnightModel.Transfinite
