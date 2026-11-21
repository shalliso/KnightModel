import KnightModel.RankTwo.NegativeTreeSystem
import Mathlib.Order.Preorder.Chain

/-! # Restriction trees as partially ordered sets

The points of a level system are pairs consisting of a height and a node.
Every strict predecessor set is order-isomorphic to the ordinal initial
segment below that height. Distinct named branches of the Kurepa alternative
are distinct ordinary maximal chains.
-/

namespace KnightModel.RankTwo.Restriction

open Cardinal Set

structure LevelTree (I : Type) [LinearOrder I] where
  level : I → Type
  down : ∀ {i j}, i ≤ j → level j → level i
  refl : ∀ {i} (x : level i), down le_rfl x = x
  trans : ∀ {i j k} (ij : i ≤ j) (jk : j ≤ k) (x : level k),
    down ij (down jk x) = down (ij.trans jk) x

namespace LevelTree
variable {I : Type} [LinearOrder I] (T : LevelTree I)

structure Point where
  height : I
  val : T.level height

namespace Point
variable {T}

def Below (p q : T.Point) : Prop := ∃ h : p.height ≤ q.height, T.down h q.val = p.val

private theorem same_height {p q : T.Point} (pq : p.Below q) (eq : p.height = q.height) : p = q := by
  obtain ⟨a,s⟩ := p
  obtain ⟨b,t⟩ := q
  change a = b at eq
  subst b
  obtain ⟨h,e⟩ := pq
  have st : t = s := (T.refl t).symm.trans e
  cases st
  rfl

instance : PartialOrder T.Point where
  le := Below
  le_refl p := ⟨le_rfl,T.refl _⟩
  le_trans _ _ _ h k := by
    obtain ⟨ab,h⟩ := h
    obtain ⟨bc,k⟩ := k
    exact ⟨ab.trans bc,(T.trans ab bc _).symm.trans ((congrArg (T.down ab) k).trans h)⟩
  le_antisymm _ _ h k := same_height h (le_antisymm h.choose k.choose)

theorem height_le {p q : T.Point} (h : p ≤ q) : p.height ≤ q.height := h.choose

theorem height_lt {p q : T.Point} (h : p < q) : p.height < q.height :=
  lt_of_le_of_ne (height_le h.le) (fun e => h.ne (same_height h.le e))

def atHeight (p : T.Point) {i : I} (h : i ≤ p.height) : T.Point := ⟨i,T.down h p.val⟩

theorem atHeight_le (p : T.Point) {i : I} (h : i ≤ p.height) : p.atHeight h ≤ p := ⟨h,rfl⟩

theorem atHeight_mono (p : T.Point) {i j : I} (hij : i ≤ j) (hj : j ≤ p.height) :
    p.atHeight (hij.trans hj) ≤ p.atHeight hj := ⟨hij,T.trans hij hj p.val⟩

/-- This identifies every predecessor order with the precise ordinal height. -/
def predecessors (p : T.Point) : Iio p ≃o Iio p.height where
  toFun q := ⟨q.val.height,height_lt q.property⟩
  invFun i := ⟨p.atHeight i.property.le,lt_of_le_of_ne (p.atHeight_le i.property.le)
    (fun e => i.property.ne (congrArg Point.height e))⟩
  left_inv q := by
    apply Subtype.ext
    obtain ⟨⟨i,s⟩,h⟩ := q
    have hp : (Point.mk i s : T.Point) ≤ p := (show (Point.mk i s : T.Point) < p from h).le
    have eq := hp.choose_spec
    exact congrArg (Point.mk i) eq
  right_inv i := by rfl
  map_rel_iff' := by
    intro q r
    constructor
    · intro h
      have rq : r.val ≤ p := (show r.val < p from r.property).le
      have qq : q.val ≤ p := (show q.val < p from q.property).le
      change q.val.height ≤ r.val.height at h
      exact ⟨h, (congrArg (T.down h) rq.choose_spec.symm).trans
        ((T.trans h _ p.val).trans qq.choose_spec)⟩
    · exact height_le

end Point

/-- The nodes of precisely height i constitute the original i-th level. -/
def atLevel (i : I) : {p : T.Point // p.height = i} ≃ T.level i where
  toFun p := p.property ▸ p.val.val
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv := by rintro ⟨⟨a,x⟩,h⟩; obtain rfl : a = i := h; rfl
  right_inv _ := rfl

def branchSet (f : ∀ i, T.level i) : Set T.Point := range (fun i => Point.mk i (f i))

theorem branch_max (f : ∀ i, T.level i) (coh : ∀ {i j} (h : i ≤ j), T.down h (f j) = f i) :
    IsMaxChain (· ≤ ·) (T.branchSet f) := by
  constructor
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ _
    rcases le_total a b with ha | hb
    · exact .inl ⟨ha,coh ha⟩
    · exact .inr ⟨hb,coh hb⟩
  · intro A hA sub
    refine Subset.antisymm sub ?_
    intro p hp
    let q : T.Point := ⟨p.height,f p.height⟩
    have hq : q ∈ T.branchSet f := ⟨p.height,rfl⟩
    by_cases e : p = q
    · exact e ▸ hq
    · rcases hA hp (sub hq) e with pq | qp
      · exact (Point.same_height pq rfl) ▸ hq
      · exact (Point.same_height qp rfl) ▸ hq

theorem branchSet_injective : Function.Injective T.branchSet := by
  intro f g eq
  funext i
  have mem : Point.mk i (f i) ∈ T.branchSet g := eq ▸ mem_range_self i
  obtain ⟨j,hj⟩ := mem
  obtain rfl : j = i := congrArg Point.height hj
  exact (eq_of_heq (Point.mk.inj hj).2).symm

end LevelTree

def SpecialTree.levelTree (T : SpecialTree) : LevelTree OmegaTwo where
  level := T.node
  down := T.down
  refl x := T.down_refl _ x
  trans := T.down_trans

def CountableLevelTree.levelTree (T : CountableLevelTree.{0,0,0} omegaOneStages OmegaTwo) :
    LevelTree OmegaOne where
  level := T.node
  down := T.down
  refl := fun x => T.down_refl _ x
  trans := T.down_trans

noncomputable def CountableLevelTree.maximalBranches (T : CountableLevelTree.{0,0,0} omegaOneStages OmegaTwo) :
    OmegaTwo ↪ {s : Set T.levelTree.Point // IsMaxChain (· ≤ ·) s ∧ ∀ i, ∃ p ∈ s, p.height = i} where
  toFun b := ⟨T.levelTree.branchSet (T.branch b), T.levelTree.branch_max _ (T.coherent b),
    fun i => ⟨⟨i,T.branch b i⟩,⟨i,rfl⟩,rfl⟩⟩
  inj' := by
    intro b c h
    exact T.separates b c (congrFun (T.levelTree.branchSet_injective (congrArg Subtype.val h)))

/-- The specializing function bounds every chain. -/
theorem SpecialTree.chain_cardinal (T : SpecialTree) {s : Set T.levelTree.Point}
    (h : IsChain (· ≤ ·) s) : #s ≤ ℵ₁ := by
  let f (p : s) := T.label p.val.val
  have ne {p q : T.levelTree.Point} (lt : p < q) : T.label p.val ≠ T.label q.val := by
    have hh := LevelTree.Point.height_lt lt
    have sub := lt.le.choose_spec
    exact sub ▸ T.special hh q.val
  have inj : Function.Injective f := by
    intro p q same
    by_contra e
    have distinct : p.val ≠ q.val := fun z => e (Subtype.ext z)
    rcases h p.property q.property distinct with pq | qp
    · exact ne (lt_of_le_of_ne pq distinct) same
    · exact ne (lt_of_le_of_ne qp distinct.symm) same.symm
  simpa only [cardinal_specializing_labels] using mk_le_of_injective inj

/-- Regularity of ω₂ rules out even a cofinal chain skipping some levels. -/
theorem SpecialTree.no_cofinal_chain (T : SpecialTree) {s : Set T.levelTree.Point}
    (h : IsChain (· ≤ ·) s) : ¬ ∀ i, ∃ p ∈ s, i ≤ p.height := by
  intro cofinal
  let ht (p : s) := p.val.height
  have hc : IsCofinal (range ht) := by
    intro i
    obtain ⟨p,hp,ip⟩ := cofinal i
    exact ⟨ht ⟨p,hp⟩,mem_range_self _,ip⟩
  have le := (Order.cof_le hc).trans ((mk_range_le (f := ht)).trans (T.chain_cardinal h))
  have regular : Cardinal.IsRegular (aleph.{0} 2) := by
    simpa only [one_add_one_eq_two] using isRegular_aleph_add_one 1
  rw [Ordinal.cof_toType, regular.cof_ord] at le
  exact (aleph_lt_aleph.mpr _root_.one_lt_two).not_ge le

end KnightModel.RankTwo.Restriction
