import KnightModel.RankTwo.RankModel

/-! # Restricting the full automorphism group to a named sort -/

namespace KnightModel.RankTwo.Scott

variable {R : Nat → Type*} {M X : Type*} (D : Model R M)

/-- An injective presentation of one sort, closed under all automorphisms of D. -/
structure InvariantSort (X : Type*) where
  incl : X → M
  injective : Function.Injective incl
  stable : ∀ (g : ↥(automorphismGroup D)) (x : X), ∃ y, incl y = g.val (incl x)

namespace InvariantSort

variable {D} (S : InvariantSort D X)

noncomputable def map (g : ↥(automorphismGroup D)) (x : X) : X :=
  (S.stable g x).choose

@[simp] theorem incl_map (g : ↥(automorphismGroup D)) (x : X) :
    S.incl (S.map g x) = g.val (S.incl x) :=
  (S.stable g x).choose_spec

/-- All action laws follow by applying the inclusion, without any choice of
lifts of automorphisms of the individual sort. -/
@[implicit_reducible] noncomputable def action : MulAction ↥(automorphismGroup D) X where
  smul := S.map
  one_smul x := S.injective (S.incl_map 1 x)
  mul_smul g h x := S.injective (by
    change S.incl (S.map (g * h) x) = S.incl (S.map g (S.map h x))
    rw [S.incl_map, S.incl_map, S.incl_map]; rfl)

/-- Restricted permutations are bijective, with the restriction of the inverse as inverse. -/
noncomputable def perm (g : ↥(automorphismGroup D)) : Equiv.Perm X where
  toFun := S.map g
  invFun := S.map g⁻¹
  left_inv x := S.injective (by
    rw [S.incl_map, S.incl_map]
    exact g.val.symm_apply_apply _)
  right_inv x := S.injective (by
    rw [S.incl_map, S.incl_map]
    exact g.val.apply_symm_apply _)

end InvariantSort

end KnightModel.RankTwo.Scott
