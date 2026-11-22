import KnightModel.Transfinite.CanonicalActions
import KnightModel.Transfinite.CanonicalFrame
import KnightModel.Transfinite.ComparisonSuccessor
import KnightModel.RankTwo.ProgramDefinabilityComplete

/-! # All finite tuples in the actual successor model

Relative to a frame above a tuple, semilinear selection recovers a tuple of
vectors, and the finite ordered supports of the vectors recover a finite tuple
of old elements. The argument applies to every seed and every nonzero ordinal.
-/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott Semilinear

namespace SuccessorAut

noncomputable section

variable (P : Seed)

local notation "A" => Concrete.smallAction P.mark
local notation "T" => smallInterpretation P.D P.mark
local notation "I" => P.M
local notation "V" => VectorGroup P.M
local notation "F" => Concrete.SmallFrames P.mark
local notation "U" => SmallCarrier P.mark
local notation "G" => (automorphismGroup (smallModel P.D P.mark) : Type _)
local notation "ix" => SuccessorAut.indexSort P
local notation "vx" => SuccessorAut.vectorSort P
local notation "fx" => SuccessorAut.frameSort P

local instance : MulAction G I := (ix).action
local instance : MulAction G V := (vx).action
local instance : MulAction G (I →₀ ℚ) := (vx).action
local instance : MulAction G F := (fx).action
local instance : MulAction G U := modelAutAction (smallModel P.D P.mark)
local instance : SMul G U := (modelAutAction (smallModel P.D P.mark)).toSMul

private theorem transitionDefinable {n : ℕ} (k : Concrete.Name n) (u v : F) :
    Definable {p : Fin n → V | (T).Transition k u v (Sum.inr ∘ p)} := by
  by_cases h : (A).Below u v
  · obtain ⟨c, hc⟩ := h
    obtain ⟨φ, hφ⟩ := Concrete.definable_run P.mark k c
    refine ⟨φ, fun p => Iff.trans ?_ (hφ p)⟩
    constructor
    · rintro ⟨b, hb, hu⟩
      exact (T).faithful v b c (hu.trans hc.symm) ▸ hb
    · exact fun hr => ⟨c, hr, hc⟩
  · exact ⟨.ltZero (.const 0), fun p =>
      iff_of_false (fun ⟨c, _, hc⟩ => h ⟨c, hc⟩) (lt_irrefl _)⟩

theorem canonicalParameters : HasCanonicalParameters G I ℚ (A).Below := by
  let rel (k : Σ n, Concrete.Name n) (u v : F) (p : Fin k.1 → I →₀ ℚ) :=
    (T).Transition k.2 u v (Sum.inr ∘ p)
  apply hasCanonicalParameters_of_semilinear_fibers (vectorAffineSamples P.mark)
    (SuccessorAut.vectorOrderIso P) (fun _ _ => rfl) (SuccessorAut.preserves_samples P)
    (show V ≃ (I →₀ ℚ) from Equiv.refl _) (fun _ _ => rfl) (A).Below
    (fun k : Σ n, Concrete.Name n => k.1) rel
  · rintro u v ⟨c, hc⟩
    obtain ⟨n, k, p, hp⟩ := Concrete.run_covers_vectors P.mark c
    exact ⟨⟨n, k⟩, p, c, hp, hc⟩
  · exact fun k _ _ v p => (T).transition_functional k.2 v (Sum.inr ∘ p)
  · exact fun g k u v p => (T).invariant_transition Sum.inr g ((fx).map g) ((vx).map g)
      ((fx).incl_map g) ((vx).incl_map g) k.2 u v p
  · exact fun k u v => transitionDefinable P k.2 u v

/-- The base points are below every frame. Frame heights need only form a
total preorder, so the invariant order later added to the seed is immaterial. -/
private def anchoredBelow : U → U → Prop
  | .inl _, _ => True
  | .inr _, .inl _ => False
  | .inr u, .inr v => (A).Below u v

private theorem below_trans {x y z : F} : (A).Below x y → (A).Below y z → (A).Below x z := by
  rintro ⟨c, rfl⟩ ⟨d, rfl⟩
  exact ⟨(A).comp d c, (A).act_comp z d c⟩

private theorem incl_fixed {R : ℕ → Type} {M X : Type} {D : Scott.Model R M}
    (S : InvariantSort D X) (g : ↥(automorphismGroup D)) (x : X) :
    g.val (S.incl x) = S.incl x ↔ S.map g x = x := by
  rw [← S.incl_map]
  exact S.injective.eq_iff

private theorem coordinateSupport (a b : U) (h : anchoredBelow P a b) :
    ∃ s, FrameSupport G I a b s := by
  classical
  cases a with
  | inl base =>
    cases base with
    | inl i =>
      refine ⟨{i}, fun g _ => ?_⟩
      simp only [Finset.mem_singleton, forall_eq]
      change g.val ((ix).incl i) = (ix).incl i ↔ (ix).map g i = i
      exact incl_fixed (ix) g i
    | inr v =>
      refine ⟨v.support, fun g _ => (incl_fixed (vx) g v).trans ?_⟩
      exact vectorSupport (SuccessorAut.index_monotone P) (SuccessorAut.coefficient_map P) v g
  | inr f =>
    cases b with
    | inl _ => exact False.elim h
    | inr b =>
      obtain ⟨s, hs⟩ := canonicalFrameSupport (SuccessorAut.index_monotone P)
        (SuccessorAut.coefficient_map P) (canonicalParameters P) h
      refine ⟨s, fun g hg => (incl_fixed (fx) g f).trans ?_⟩
      exact hs g ((incl_fixed (fx) g b).mp hg)

/-- The finite support comparison in the actual full automorphism action. -/
theorem tupleSupports {n : ℕ} (x y : Fin n → U) :
    (∃ s : Finset I, ∀ g : G, g • y = y → (g • x = x ↔ ∀ i ∈ s, g • i = i)) ∨
    (∃ s : Finset I, ∀ g : G, g • x = x → (g • y = y ↔ ∀ i ∈ s, g • i = i)) := by
  apply compareTupleSupports (anchoredBelow P) _ _ (coordinateSupport P) x y
  · rintro (a | a) (b | b)
    · exact Or.inl trivial
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact (A).below_total a b
  · rintro (a | a) (b | b) (c | c)
    all_goals first
      | exact fun _ _ => trivial
      | exact fun h _ => False.elim h
      | exact fun _ h => False.elim h
      | exact below_trans P

/-- One of two arbitrary points is fixed by the stabilizer of the other point
and a finite tuple of old elements. This form transfers to every Scott model. -/
theorem pair_dependence (a b : U) :
    (∃ s : List I, ModelRankLE (smallModel P.D P.mark) 0 (b :: s.map (indexIn P)) a) ∨
    (∃ s : List I, ModelRankLE (smallModel P.D P.mark) 0 (a :: s.map (indexIn P)) b) := by
  classical
  have extract (x y : U) (h : anchoredBelow P x y) :
      ∃ s : List I, ModelRankLE (smallModel P.D P.mark) 0 (y :: s.map (indexIn P)) x := by
    obtain ⟨s, hs⟩ := coordinateSupport P x y h
    refine ⟨s.toList, fun g hg => (hs g (hg y List.mem_cons_self)).mpr ?_⟩
    intro i hi
    apply (incl_fixed (ix) g i).mp
    apply hg
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)
  apply Or.imp (extract a b) (extract b a)
  cases a with
  | inl => exact Or.inl trivial
  | inr a =>
    cases b with
    | inl => exact Or.inr trivial
    | inr b => exact (A).below_total a b

end

end SuccessorAut

/-- A uniform strict comparison bound on old finite tuples yields the weak
bound on every finite tuple of the successor, for its full automorphism group. -/
theorem successor_tuple_comparisonLE (P : Seed) {α : Ordinal.{w}} (hα : α ≠ 0)
    (old : ∀ n (p : Fin n → P.M), ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup P.D)) p)
    (n : ℕ) (x : Fin n → SmallCarrier P.mark) :
    ComparisonLE α (⊤ : Subgroup ↥(automorphismGroup (smallModel P.D P.mark))) x := by
  let G := ↥(automorphismGroup (smallModel P.D P.mark))
  letI : MulAction G P.M := (SuccessorAut.indexSort P).action
  have old' (n : ℕ) (p : Fin n → P.M) : ComparisonLT α (⊤ : Subgroup G) p := by
    obtain ⟨β, hb, hr⟩ := old n p
    refine ⟨β, hb, ComparisonLE.of_hom (J := ⊤) (y := p) (SuccessorAut.forget P) ?_ ?_ hr⟩
    · exact fun _ _ => trivial
    · exact fun _ _ => Iff.rfl
  apply comparisonLE_of_coded_conjugates hα old'
  intro g _
  rcases SuccessorAut.tupleSupports P x (g • x) with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl (CodedBy.of_finset s fun h hh => hs h hh.2)
  · exact Or.inr (CodedBy.of_finset s fun h hh => hs h hh.2)

end KnightModel.Transfinite
