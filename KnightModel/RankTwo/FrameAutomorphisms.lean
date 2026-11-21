import KnightModel.RankTwo.BaseLanguage
import KnightModel.RankTwo.SortAction
import KnightModel.RankTwo.VectorSampling

/-!
# Recovering the three sort actions from the full relational automorphism group

The unary predicates recover the sorts of the index, vector and frame variables.
The graph of each Knight function forces the index action to fix everything below
a fixed index, and the named rational coefficients determine the vector action.
-/

namespace KnightModel.RankTwo.Scott

open Set

variable {Ω I C F : Type} [Blueprint Ω] [KnightModel I Ω] {K : Nat → Type}
    {A : FrameAction C F} (i₀ : I) (T : FrameInterpretation (BaseRelation Ω) K (BasePoints I) A)
    (base_eq : ∀ {n} (r : BaseRelation Ω n) t, T.base r t ↔ baseModel i₀ r t)

local notation "U" => BasePoints I ⊕ F
local notation "G" => (automorphismGroup T.model : Type _)

def indexIn (x : I) : U := .inl (.inl x)
def vectorIn (v : VectorGroup I) : U := .inl (.inr v)
def frameIn (f : F) : U := .inr f

include base_eq in
private theorem base_iff {n : ℕ} (r : BaseRelation Ω n) (t : Tuple (BasePoints I) n) :
    T.model (.base r) (Sum.inl ∘ t) ↔ baseModel i₀ r t := by
  constructor
  · rintro ⟨v, hv, hr⟩
    have he : t = v := funext fun j => Sum.inl.inj (hv j)
    exact he ▸ (base_eq _ _).mp hr
  · intro h
    exact ⟨t, fun _ => rfl, (base_eq _ _).mpr h⟩

include base_eq in
private theorem indexPred (u : U) :
    T.model (.base .indexSort) (fun _ => u) ↔ ∃ x : I, indexIn x = u := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hx⟩ := (base_eq _ _).mp h
    exact ⟨x, (congrArg Sum.inl hx.symm).trans (hv 0).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun _ => .inl x, fun _ => rfl, (base_eq _ _).mpr ⟨x, rfl⟩⟩

include base_eq in
private theorem vectorPred (u : U) :
    T.model (.base .vectorSort) (fun _ => u) ↔ ∃ v : VectorGroup I, vectorIn v = u := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hx⟩ := (base_eq _ _).mp h
    exact ⟨x, (congrArg Sum.inl hx.symm).trans (hv 0).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨fun _ => .inr v, fun _ => rfl, (base_eq _ _).mpr ⟨v, rfl⟩⟩

private def unarySort {R : Nat → Type} {M X : Type} (D : Model R M) (r : R 1)
    (f : X → M) (h : Function.Injective f)
    (defn : ∀ y, D r (fun _ => y) ↔ ∃ x, f x = y) : InvariantSort D X where
  incl := f
  injective := h
  stable g x := (defn _).mp ((g.property r (fun _ => f x)).mp ((defn _).mpr ⟨x, rfl⟩))

def indexSort : InvariantSort T.model I :=
  unarySort T.model (.base .indexSort) indexIn (fun _ _ h => Sum.inl.inj (Sum.inl.inj h))
    (indexPred i₀ T base_eq)

def vectorSort : InvariantSort T.model (VectorGroup I) :=
  unarySort T.model (.base .vectorSort) vectorIn (fun _ _ h => Sum.inr.inj (Sum.inl.inj h))
    (vectorPred i₀ T base_eq)

def frameSort : InvariantSort T.model F :=
  unarySort T.model .frame frameIn (fun _ _ h => Sum.inr.inj h)
    (fun _ => exists_congr fun _ => eq_comm)

-- The maps below are the restrictions of one and the same permutation.
local notation "ix" => indexSort i₀ T base_eq
local notation "vx" => vectorSort i₀ T base_eq
local notation "fx" => frameSort T

include base_eq in
private theorem coordMap {n : ℕ} (g : G) (r : BaseRelation Ω n)
    (s t : Tuple (BasePoints I) n)
    (h : ∀ j, Sum.inl (t j) = g.val (.inl (s j))) :
    baseModel i₀ r s ↔ baseModel i₀ r t := by
  rw [← base_iff i₀ T base_eq r s, ← base_iff i₀ T base_eq r t]
  have he : g.val ∘ (Sum.inl ∘ s) = Sum.inl ∘ t := funext fun j => (h j).symm
  exact he ▸ g.property (.base r) (Sum.inl ∘ s)

private theorem index_base_iff {n : ℕ} (r : IndexRelation Ω n) (s : Tuple I n) :
    baseModel i₀ (.index r) (Sum.inl ∘ s) ↔ indexModel i₀ r s := by
  constructor
  · rintro ⟨t, ht, hr⟩
    have he : s = t := funext fun j => Sum.inl.inj (ht j)
    exact he ▸ hr
  · exact fun h => ⟨s, fun _ => rfl, h⟩

theorem index_rel {n : ℕ} (g : G) (r : IndexRelation Ω n) (s : Tuple I n) :
    indexModel i₀ r s ↔ indexModel i₀ r ((ix).map g ∘ s) := by
  rw [← index_base_iff i₀ r, ← index_base_iff i₀ r]
  exact coordMap i₀ T base_eq g (.index r) _ _ (fun j => (ix).incl_map g (s j))

theorem index_monotone (g : G) : Monotone ((ix).map g) := by
  intro x y h
  exact (index_rel i₀ T base_eq g .order (Fin.cons x (fun _ => y))).mp h

theorem index_commutes (g : G) (c : Ω) (x : I) :
    (ix).map g (KnightModel.fn c x) = KnightModel.fn c ((ix).map g x) :=
  (index_rel i₀ T base_eq g (.graph c) (Fin.cons x (fun _ => KnightModel.fn c x))).mp rfl

theorem index_fixes_mark (g : G) : (ix).map g i₀ = i₀ :=
  (index_rel i₀ T base_eq g .mark (fun _ => i₀)).mp rfl

theorem coefficient_map (g : G) (v : VectorGroup I) (x : I) :
    ((vx).map g v) ((ix).map g x) = v x := by
  let s : Tuple (BasePoints I) 2 := Fin.cons (.inr v) (fun _ => .inl x)
  let t : Tuple (BasePoints I) 2 := Fin.cons (.inr ((vx).map g v)) (fun _ => .inl ((ix).map g x))
  have hrel := coordMap i₀ T base_eq g (.coefficient (v x)) s t (fun j =>
    Fin.cases ((vx).incl_map g v) (fun _ => (ix).incl_map g x) j)
  obtain ⟨w,j,hw,hj,hh⟩ := hrel.mp ⟨v,x,rfl,rfl,rfl⟩
  obtain rfl := Sum.inr.inj (show Sum.inr ((vx).map g v) = Sum.inr w from hw)
  obtain rfl := Sum.inl.inj (show Sum.inl ((ix).map g x) = Sum.inl j from hj)
  exact hh

/-- The permutation induced on the index sort preserves the Knight order. -/
noncomputable def indexOrderIso (g : G) : I ≃o I where
  toEquiv := (ix).perm g
  map_rel_iff' := by
    intro x y
    exact (index_rel i₀ T base_eq g .order (Fin.cons x (fun _ => y))).symm

private theorem vector_strictMono (g : G) : StrictMono ((vx).map g) := by
  let e := indexOrderIso i₀ T base_eq g
  intro v w h
  obtain ⟨i, hg, hi⟩ := Finsupp.Colex.lt_iff.mp h
  apply Finsupp.Colex.lt_iff.mpr
  refine ⟨e i, ?_, ?_⟩
  · intro j hj
    obtain ⟨k, rfl⟩ := e.surjective j
    exact (coefficient_map i₀ T base_eq g v k).trans
      ((hg k (e.lt_iff_lt.mp hj)).trans (coefficient_map i₀ T base_eq g w k).symm)
  · exact (coefficient_map i₀ T base_eq g v i).symm ▸
      ((coefficient_map i₀ T base_eq g w i).symm ▸ hi)

/-- The colex order is recovered from the coefficient and index relations. -/
noncomputable def vectorOrderIso (g : G) : VectorGroup I ≃o VectorGroup I where
  toEquiv := (vx).perm g
  map_rel_iff' := (vector_strictMono i₀ T base_eq g).le_iff_le

@[simp] theorem vectorOrderIso_apply (g : G) (x : VectorGroup I) :
    vectorOrderIso i₀ T base_eq g x = (vx).map g x := rfl

/-- The underlying vector permutation preserves sums and rational scalar multiples. -/
noncomputable def vectorLinearMap (g : G) : VectorGroup I →ₗ[ℚ] VectorGroup I where
  toFun := (vx).map g
  map_add' x y := by
    apply Finsupp.ext
    intro j
    obtain ⟨k, rfl⟩ := ((ix).perm g).surjective j
    change ((vx).map g (x + y)) ((ix).map g k) = ((vx).map g x) ((ix).map g k) +
      ((vx).map g y) ((ix).map g k)
    simp only [coefficient_map]
    rfl
  map_smul' q x := by
    apply Finsupp.ext
    intro j
    obtain ⟨k, rfl⟩ := ((ix).perm g).surjective j
    change ((vx).map g (q • x)) ((ix).map g k) = q * (((vx).map g x) ((ix).map g k))
    simp only [coefficient_map]
    rfl

private theorem vector_fixes_unit (g : G) :
    (vx).map g (unitLetter i₀).val = (unitLetter i₀).val := by
  classical
  apply Finsupp.ext
  intro j
  let e := indexOrderIso i₀ T base_eq g
  obtain ⟨k, rfl⟩ := e.surjective j
  change ((vx).map g (unitLetter i₀).val) ((ix).map g k) = (unitLetter i₀).val (e k)
  rw [coefficient_map]
  have he : e i₀ = i₀ := index_fixes_mark i₀ T base_eq g
  by_cases hk : k = i₀
  · subst k; rw [he]
  · have h' : e k ≠ i₀ := fun hh => hk (e.injective (hh.trans he.symm))
    simp [unitLetter, Finsupp.single_eq_of_ne hk, Finsupp.single_eq_of_ne h']

/-- Every automorphism of the full three-sorted structure preserves the
canonical interval sample operations on its vector sort. -/
theorem preserves_samples (g : G) :
    UnaryChoice.Preserves (P := vectorSamples (unitLetter i₀).val (unitLetter_pos i₀))
      (vectorOrderIso i₀ T base_eq g) :=
  preserves_vectorSamples (unitLetter_pos i₀) (vectorOrderIso i₀ T base_eq g)
    (vectorLinearMap i₀ T base_eq g) (fun _ => rfl) (vector_fixes_unit i₀ T base_eq g)

end KnightModel.RankTwo.Scott
