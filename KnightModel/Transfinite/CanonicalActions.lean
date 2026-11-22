import KnightModel.Transfinite.Seed
import KnightModel.Transfinite.SuccessorModel
import KnightModel.RankTwo.RankNamedFrames

/-! # Automorphisms of the actual successor structure

The old language is named in the successor. Restriction to this sort yields
an actual automorphism of the input model. The coefficient relations determine
the action on the vector sort and the canonical semilinear choice operations.
-/

namespace KnightModel.Transfinite.SuccessorAut

open RankTwo RankTwo.Scott Set

variable (P : Seed)

local notation "T" => smallInterpretation P.D P.mark
local notation "I" => P.M
local notation "V" => VectorGroup P.M
local notation "F" => Concrete.SmallFrames P.mark
local notation "U" => SmallCarrier P.mark
local notation "G" => (automorphismGroup (smallModel P.D P.mark) : Type _)
def indexIn (x : I) : U := .inl (.inl x)
def vectorIn (v : VectorGroup I) : U := .inl (.inr v)
def frameIn (f : F) : U := .inr f

private theorem base_iff {n : ℕ} (r : Transfinite.BaseRelation P.R n) (t : Tuple (BasePoints I) n) :
    (T).model (.base r) (Sum.inl ∘ t) ↔ Transfinite.baseModel P.D r t := by
  constructor
  · rintro ⟨v, hv, hr⟩
    have he : t = v := funext fun j => Sum.inl.inj (hv j)
    exact he ▸ hr
  · intro h
    exact ⟨t, fun _ => rfl, h⟩

theorem indexPred (u : U) :
    (T).model (.base .indexSort) (fun _ => u) ↔ ∃ x : I, indexIn P x = u := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hx⟩ := h
    exact ⟨x, (congrArg Sum.inl hx.symm).trans (hv 0).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun _ => .inl x, fun _ => rfl, ⟨x, rfl⟩⟩

private theorem vectorPred (u : U) :
    (T).model (.base .vectorSort) (fun _ => u) ↔ ∃ v : VectorGroup I, vectorIn P v = u := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨x, hx⟩ := h
    exact ⟨x, (congrArg Sum.inl hx.symm).trans (hv 0).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨fun _ => .inr v, fun _ => rfl, ⟨v, rfl⟩⟩

private def unarySort {R : Nat → Type} {M X : Type} (D : Model R M) (r : R 1)
    (f : X → M) (h : Function.Injective f)
    (defn : ∀ y, D r (fun _ => y) ↔ ∃ x, f x = y) : InvariantSort D X where
  incl := f
  injective := h
  stable g x := (defn _).mp ((g.property r (fun _ => f x)).mp ((defn _).mpr ⟨x, rfl⟩))

def indexSort : InvariantSort (T).model I :=
  unarySort (T).model (.base .indexSort) (indexIn P) (fun _ _ h => Sum.inl.inj (Sum.inl.inj h))
    (indexPred P)

def vectorSort : InvariantSort (T).model (VectorGroup I) :=
  unarySort (T).model (.base .vectorSort) (vectorIn P) (fun _ _ h => Sum.inr.inj (Sum.inl.inj h))
    (vectorPred P)

def frameSort : InvariantSort (T).model F :=
  unarySort (T).model .frame (frameIn P) (fun _ _ h => Sum.inr.inj h)
    (fun _ => exists_congr fun _ => eq_comm)

-- The maps below are the restrictions of one and the same permutation.
local notation "ix" => indexSort P
local notation "vx" => vectorSort P
local notation "fx" => frameSort P

private theorem coordMap {n : ℕ} (g : G) (r : Transfinite.BaseRelation P.R n)
    (s t : Tuple (BasePoints I) n)
    (h : ∀ j, Sum.inl (t j) = g.val (.inl (s j))) :
    Transfinite.baseModel P.D r s ↔ Transfinite.baseModel P.D r t := by
  rw [← base_iff P r s, ← base_iff P r t]
  have he : g.val ∘ (Sum.inl ∘ s) = Sum.inl ∘ t := funext fun j => (h j).symm
  exact he ▸ g.property (.base r) (Sum.inl ∘ s)

private theorem old_base_iff {n : ℕ} (r : P.R n) (s : Tuple I n) :
    Transfinite.baseModel P.D (.old r) (Sum.inl ∘ s) ↔ P.D r s := by
  constructor
  · rintro ⟨t, ht, hr⟩
    have he : s = t := funext fun j => Sum.inl.inj (ht j)
    exact he ▸ hr
  · exact fun h => ⟨s, fun _ => rfl, h⟩

/-- The induced structure on the named old sort is exactly the input structure. -/
theorem oldModel_iff {n : ℕ} (r : P.R n) (s : Tuple I n) :
    smallModel P.D P.mark (.base (.old r)) (indexIn P ∘ s) ↔ P.D r s :=
  (base_iff P _ (Sum.inl ∘ s)).trans (old_base_iff P r s)

theorem old_rel {n : ℕ} (g : G) (r : P.R n) (s : Tuple I n) :
    P.D r s ↔ P.D r ((ix).map g ∘ s) := by
  rw [← old_base_iff P r, ← old_base_iff P r]
  exact coordMap P g (.old r) _ _ (fun j => (ix).incl_map g (s j))

/-- The restriction homomorphism to the full old automorphism group. -/
noncomputable def forget : G →* automorphismGroup P.D where
  toFun g := ⟨(ix).perm g, fun r t => old_rel P g r t⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    exact fun x => (ix).action.one_smul x
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    exact fun x => (ix).action.mul_smul g h x

theorem index_monotone (g : G) : Monotone ((ix).map g) := by
  intro x y h
  let t : Tuple I 2 := Fin.cons x (fun _ => y)
  exact (P.le_iff _).mp ((old_rel P g P.leSym t).mp ((P.le_iff _).mpr h))

theorem index_fixes_mark (g : G) : (ix).map g P.mark = P.mark :=
  (P.mark_iff _).mp ((old_rel P g P.markSym (fun _ => P.mark)).mp ((P.mark_iff _).mpr rfl))

theorem coefficient_map (g : G) (v : VectorGroup I) (x : I) :
    ((vx).map g v) ((ix).map g x) = v x := by
  let s : Tuple (BasePoints I) 2 := Fin.cons (.inr v) (fun _ => .inl x)
  let t : Tuple (BasePoints I) 2 := Fin.cons (.inr ((vx).map g v)) (fun _ => .inl ((ix).map g x))
  have hrel := coordMap P g (.coefficient (v x)) s t (fun j =>
    Fin.cases ((vx).incl_map g v) (fun _ => (ix).incl_map g x) j)
  obtain ⟨w,j,hw,hj,hh⟩ := hrel.mp ⟨v,x,rfl,rfl,rfl⟩
  obtain rfl := Sum.inr.inj (show Sum.inr ((vx).map g v) = Sum.inr w from hw)
  obtain rfl := Sum.inl.inj (show Sum.inl ((ix).map g x) = Sum.inl j from hj)
  exact hh

/-- The permutation induced on the index sort preserves the named order. -/
noncomputable def indexOrderIso (g : G) : I ≃o I where
  toEquiv := (ix).perm g
  map_rel_iff' := by
    intro x y
    let t : Tuple I 2 := Fin.cons x (fun _ => y)
    exact ((P.le_iff t).symm.trans ((old_rel P g P.leSym t).trans (P.le_iff _))).symm

private theorem vector_strictMono (g : G) : StrictMono ((vx).map g) := by
  let e := indexOrderIso P g
  intro v w h
  obtain ⟨i, hg, hi⟩ := Finsupp.Colex.lt_iff.mp h
  apply Finsupp.Colex.lt_iff.mpr
  refine ⟨e i, ?_, ?_⟩
  · intro j hj
    obtain ⟨k, rfl⟩ := e.surjective j
    exact (coefficient_map P g v k).trans
      ((hg k (e.lt_iff_lt.mp hj)).trans (coefficient_map P g w k).symm)
  · exact (coefficient_map P g v i).symm ▸
      ((coefficient_map P g w i).symm ▸ hi)

/-- The colex order is recovered from the coefficient and index relations. -/
noncomputable def vectorOrderIso (g : G) : VectorGroup I ≃o VectorGroup I where
  toEquiv := (vx).perm g
  map_rel_iff' := (vector_strictMono P g).le_iff_le

@[simp] theorem vectorOrderIso_apply (g : G) (x : VectorGroup I) :
    vectorOrderIso P g x = (vx).map g x := rfl

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
    (vx).map g (unitLetter P.mark).val = (unitLetter P.mark).val := by
  classical
  apply Finsupp.ext
  intro j
  let e := indexOrderIso P g
  obtain ⟨k, rfl⟩ := e.surjective j
  change ((vx).map g (unitLetter P.mark).val) ((ix).map g k) = (unitLetter P.mark).val (e k)
  rw [coefficient_map]
  have he : e P.mark = P.mark := index_fixes_mark P g
  by_cases hk : k = P.mark
  · subst k; rw [he]
  · have h' : e k ≠ P.mark := fun hh => hk (e.injective (hh.trans he.symm))
    simp [unitLetter, Finsupp.single_eq_of_ne hk, Finsupp.single_eq_of_ne h']

/-- Every automorphism of the full three-sorted structure preserves the
canonical interval sample operations on its vector sort. -/
theorem preserves_samples (g : G) :
    UnaryChoice.Preserves (P := vectorSamples (unitLetter P.mark).val (unitLetter_pos P.mark))
      (vectorOrderIso P g) :=
  preserves_vectorSamples (unitLetter_pos P.mark) (vectorOrderIso P g)
    (vectorLinearMap P g) (fun _ => rfl) (vector_fixes_unit P g)

end KnightModel.Transfinite.SuccessorAut
