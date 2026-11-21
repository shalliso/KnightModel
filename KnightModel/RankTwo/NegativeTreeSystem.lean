import KnightModel.RankTwo.RestrictionSpecial

/-! # An indexed special ω₂-tree from narrow levels

A closed chart prefix is a node, independently of which row supplies it.
The predecessor at each earlier level is ordinary restriction. The
specializing label separates every two strictly comparable nodes.
-/

namespace KnightModel.RankTwo.Restriction

open Cardinal Set

local instance : NoMaxOrder OmegaTwo := Cardinal.noMaxOrder (aleph0_le_aleph 2)

/-- An ω₂-tree in level notation with coherent, unique predecessor maps and
an ℵ₁-valued specializing function. -/
structure SpecialTree where
  node : OmegaTwo → Type
  exists_node : ∀ a, Nonempty (node a)
  narrow : ∀ a, #(node a) ≤ ℵ₁
  down : ∀ {a b}, a ≤ b → node b → node a
  down_refl : ∀ a (t : node a), down le_rfl t = t
  down_trans : ∀ {a b c} (h : a ≤ b) (k : b ≤ c) (t : node c), down h (down k t) = down (h.trans k) t
  label : ∀ {a}, node a → ℕ × OmegaOne × OmegaOne
  special : ∀ {a b} (h : a < b) (t : node b), label (down h.le t) ≠ label t

/-- In particular no branch meets all ω₂ levels. -/
theorem SpecialTree.no_branch (T : SpecialTree) :
    ¬ ∃ f : ∀ a, T.node a, ∀ {a b} (h : a ≤ b), T.down h (f b) = f a := by
  rintro ⟨f,h⟩
  let label (a : OmegaTwo) := T.label (f a)
  have neq {a b : OmegaTwo} (ab : a < b) : label a ≠ label b := by
    simpa only [h ab.le] using T.special ab (f b)
  have inj : Function.Injective label := fun {a b} e =>
    le_antisymm (le_of_not_gt (fun g => neq g e.symm)) (le_of_not_gt (fun g => neq g e))
  have card := mk_le_of_injective inj
  rw [cardinal_specializing_labels] at card
  simp at card

namespace ClosedLevel

variable (rows : OmegaTwo → Chart OmegaTwo)

abbrev Node (a : OmegaTwo) := {t : Chart (Iic a) // ∃ b > a, t = (rows b).comap Subtype.val}

private def down {a b : OmegaTwo} (h : a ≤ b) (t : Node rows b) : Node rows a := by
  let incl (x : Iic a) : Iic b := ⟨x.val,x.property.trans h⟩
  refine ⟨t.val.comap incl,?_⟩
  obtain ⟨c,bc,hc⟩ := t.property
  exact ⟨c,h.trans_lt bc,by rw [hc]; rfl⟩

private theorem small (narrow : ∀ a, #(chartLevel rows a) ≤ ℵ₁) (a : OmegaTwo) :
    #(Node rows a) ≤ ℵ₁ := by
  classical
  obtain ⟨j,hj,hmin⟩ := wellFounded_lt.has_min (Ioi a) (by obtain ⟨b,hb⟩ := exists_gt a; exact ⟨b,hb⟩)
  change a < j at hj
  let f (t : chartLevel rows j) : Node rows a := by
    let incl (x : Iic a) : Iio j := ⟨x.val,lt_of_le_of_lt (show x.val ≤ a from x.property) hj⟩
    refine ⟨t.val.comap incl,?_⟩
    obtain ⟨c,jc,hc⟩ := t.property
    exact ⟨c,lt_of_lt_of_le hj jc,by rw [hc]; rfl⟩
  have onto : Function.Surjective f := by
    rintro ⟨t,c,ac,rfl⟩
    have jc : j ≤ c := le_of_not_gt (hmin c ac)
    exact ⟨⟨(rows c).comap Subtype.val,c,jc,rfl⟩,rfl⟩
  exact (mk_le_of_surjective onto).trans (narrow j)

private noncomputable def repr {a : OmegaTwo} (t : Node rows a) : ClosedPrefix :=
  ⟨a, t.property.choose, t.property.choose_spec.1⟩

private theorem agree_down {a b : OmegaTwo} (h : a ≤ b) (t : Node rows b) :
    AgreeThrough (rows (repr rows (down rows h t)).endpoint) (rows (repr rows t).endpoint) a := by
  let s := down rows h t
  have hs := s.property.choose_spec.2
  have ht := t.property.choose_spec.2
  constructor
  · intro x hx
    exact (congrArg (fun c : Chart (Iic a) => c.color ⟨x,hx⟩) hs).symm.trans
      (congrArg (fun c : Chart (Iic b) => c.color ⟨x,hx.trans h⟩) ht)
  · intro x hx y hy
    exact iff_of_eq ((congrArg (fun c : Chart (Iic a) => c.rel ⟨x,hx⟩ ⟨y,hy⟩) hs).symm.trans
      (congrArg (fun c : Chart (Iic b) => c.rel ⟨x,hx.trans h⟩ ⟨y,hy.trans h⟩) ht))

noncomputable def tree (H : LocalCharts rows) (tr : TransitiveRows rows)
    (narrow : ∀ a, #(chartLevel rows a) ≤ ℵ₁) : SpecialTree where
  node := Node rows
  exists_node a := by
    obtain ⟨b,ab⟩ := exists_gt a
    exact ⟨⟨(rows b).comap Subtype.val,b,ab,rfl⟩⟩
  narrow := small rows narrow
  down := down rows
  down_refl _ _ := rfl
  down_trans _ _ _ := rfl
  label t := (repr rows t).label H tr
  special h t := label_separates H tr _ _ h (agree_down rows h.le t)

end ClosedLevel

/-- The two alternatives expressed as genuine indexed trees. -/
theorem special_or_kurepa {rows : OmegaTwo → Chart OmegaTwo}
    (H : LocalCharts rows) (tr : TransitiveRows rows) (small : SmallTraces rows) :
    Nonempty SpecialTree ∨ Nonempty (CountableLevelTree.{0,0,0} omegaOneStages OmegaTwo) := by
  rcases restriction_tree_alternative H small with ⟨narrow,_⟩ | kurepa
  · exact Or.inl ⟨ClosedLevel.tree rows H tr narrow⟩
  · exact Or.inr kurepa

end KnightModel.RankTwo.Restriction
