import KnightModel.Transfinite.SumSeed
import KnightModel.Transfinite.ComparisonLimit
import KnightModel.RankTwo.RankModel

/-! # Comparison ranks in the countable ordered sum

Every automorphism restricts to a component automorphism. The finite tuple
comparison theorem then bounds mixed tuples strictly below a limit ordinal.
-/

namespace KnightModel.Transfinite
open RankTwo.Scott
namespace NamedSum
variable {R : ℕ → ℕ → Type} {X : ℕ → Type} {D : ∀ i, Model (R i) (X i)}
  {leSym : ∀ i, R i 2}
private abbrev GroupSum (D : ∀ i, Model (R i) (X i)) (leSym : ∀ i, R i 2) :=
  ↥(automorphismGroup (model D leSym))

private theorem stays (g : GroupSum D leSym) (i : ℕ) (x : X i) :
    ∃ y : X i, inject i y = g.val (inject i x) := by
  have h : tag (g.val (inject i x)) = i :=
    (g.property (.tag i) (fun _ => inject i x)).mp rfl
  generalize he : g.val (inject i x) = a at h ⊢
  obtain ⟨j,y⟩ := a
  change j = i at h
  subst j
  exact ⟨y,rfl⟩

private noncomputable def component (g : GroupSum D leSym) (i : ℕ) (x : X i) : X i :=
  (stays g i x).choose

private theorem component_spec (g : GroupSum D leSym) (i : ℕ) (x : X i) :
    inject i (component g i x) = g.val (inject i x) := (stays g i x).choose_spec

private noncomputable def permComponent (g : GroupSum D leSym) (i : ℕ) : Equiv.Perm (X i) where
  toFun := component g i
  invFun := component g⁻¹ i
  left_inv x := inject_injective i (by
    rw [component_spec,component_spec]; exact g.val.symm_apply_apply _)
  right_inv x := inject_injective i (by
    rw [component_spec,component_spec]; exact g.val.apply_symm_apply _)

/-- Restriction of actual automorphisms to the named component. -/
noncomputable def componentHom (i : ℕ) : GroupSum D leSym →* ↥(automorphismGroup (D i)) where
  toFun g := ⟨permComponent g i, by
    intro n r s
    have map := g.property (.block i r) (inject i ∘ s)
    have eq : g.val ∘ (inject i ∘ s) = inject i ∘ (permComponent g i ∘ s) :=
      funext fun l => (component_spec g i (s l)).symm
    change Block D i r (inject i ∘ s) ↔ Block D i r (g.val ∘ (inject i ∘ s)) at map
    rwa [eq,onBlock,onBlock] at map⟩
  map_one' := Subtype.ext (Equiv.ext (fun x => inject_injective i (component_spec 1 i x)))
  map_mul' g h := Subtype.ext (Equiv.ext (fun x => inject_injective i (by
    change inject i (component (g*h) i x) = inject i (component g i (component h i x))
    rw [component_spec,component_spec,component_spec]
    rfl)))

theorem component_comparison {α : Ordinal} (i : ℕ) (x : X i)
    (hr : ComparisonLE α (⊤ : Subgroup ↥(automorphismGroup (D i))) x) :
    ComparisonLE α (⊤ : Subgroup (GroupSum D leSym)) (inject i x) := by
  refine ComparisonLE.of_hom (componentHom (D := D) (leSym := leSym) i)
    (fun _ _ => Subgroup.mem_top _) ?_ hr
  intro g _
  change component g i x = x ↔ g.val (inject i x) = inject i x
  rw [← component_spec]
  exact (inject_injective i).eq_iff.symm

end NamedSum

theorem sumSeed_tuple_lt (P : ℕ → Seed) {α : Ordinal} (lim : Order.IsSuccLimit α)
    (hr : ∀ i (x : (P i).M), ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup (P i).D)) x)
    {n : ℕ} (x : Fin n → (sumSeed P).M) :
    ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup (sumSeed P).D)) x := by
  apply comparisonLT_tuple lim
  intro l
  obtain ⟨i,y⟩ := x l
  obtain ⟨β,hβ,rank⟩ := hr i y
  exact ⟨β,hβ,NamedSum.component_comparison (D := fun j => (P j).D)
    (leSym := fun j => (P j).leSym) i y rank⟩

end KnightModel.Transfinite
