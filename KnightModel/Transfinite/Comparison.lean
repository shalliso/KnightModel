import KnightModel.RankTwo.RankOrdinal
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Action.Pi

/-! # Ordinal comparison rank of a group action

The comparison clause of disjointifying rank uses only the current orbit and
the stabilizers of two conjugates. Keeping the ambient subgroup explicit lets
the same predicate apply to points, finite tuples, and tuples of parameters
from a different sort.
-/

namespace KnightModel.Transfinite

universe w

variable {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]

/-- The ordinal rank bound obtained using just the comparison clause. -/
noncomputable def ComparisonLE (α : Ordinal.{w}) (H : Subgroup G) (x : X) : Prop :=
  if α = 0 then ∀ h ∈ H, h • x = x
  else ∀ g ∈ H,
    (∃ β, ∃ _ : β < α, ComparisonLE β (H ⊓ MulAction.stabilizer G (g • x)) x) ∨
    (∃ β, ∃ _ : β < α, ComparisonLE β (H ⊓ MulAction.stabilizer G x) (g • x))
termination_by α

/-- An upper bound strictly below a given ordinal. -/
def ComparisonLT (α : Ordinal.{w}) (H : Subgroup G) (x : X) : Prop :=
  ∃ β < α, ComparisonLE β H x

@[simp] theorem comparisonLE_zero (H : Subgroup G) (x : X) :
    ComparisonLE (0 : Ordinal.{w}) H x ↔ ∀ g ∈ H, g • x = x := by
  rw [ComparisonLE, if_pos rfl]

theorem comparisonLE_iff_of_ne_zero {α : Ordinal.{w}} (hα : α ≠ 0) (H : Subgroup G) (x : X) :
    ComparisonLE α H x ↔ ∀ g ∈ H,
      ComparisonLT α (H ⊓ MulAction.stabilizer G (g • x)) x ∨
      ComparisonLT α (H ⊓ MulAction.stabilizer G x) (g • x) := by
  rw [ComparisonLE, if_neg hα]
  simp only [ComparisonLT, exists_prop]

private theorem fixes_translate_iff (g h : G) (x : X) :
    h • (g • x) = g • x ↔ (g⁻¹ * h * g) • x = x := by
  constructor
  · intro hyp
    simp only [mul_smul, hyp, inv_smul_smul]
  · intro hyp
    have hh := congrArg (g • ·) hyp
    simpa only [mul_smul, smul_inv_smul] using hh

/-- Restrict an action along a group homomorphism. Only the stabilizer of the
selected point inside the source subgroup must agree. -/
theorem ComparisonLE.of_hom {α : Ordinal.{w}} {H : Subgroup G} {J : Subgroup K} {x : X} {y : Y}
    (φ : G →* K) (maps : ∀ g ∈ H, φ g ∈ J)
    (fix : ∀ g ∈ H, φ g • y = y ↔ g • x = x) (rank : ComparisonLE α J y) :
    ComparisonLE α H x := by
  induction α using WellFoundedLT.induction generalizing H J x y with
  | ind α ih =>
    by_cases hα : α = 0
    · subst α
      exact (comparisonLE_zero ..).2 fun g hg =>
        (fix g hg).1 ((comparisonLE_zero ..).1 rank _ (maps g hg))
    rw [comparisonLE_iff_of_ne_zero hα] at rank ⊢
    intro g hg
    have translated (h : G) (hh : h ∈ H) :
        φ h • (φ g • y) = φ g • y ↔ h • (g • x) = g • x := by
      rw [fixes_translate_iff, fixes_translate_iff]
      simpa only [map_mul, map_inv] using
        fix (g⁻¹ * h * g) (H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
    rcases rank _ (maps g hg) with ⟨β, hβ, hr⟩ | ⟨β, hβ, hr⟩
    · exact Or.inl ⟨β, hβ, ih β hβ (J := J ⊓ MulAction.stabilizer K (φ g • y))
        (fun h hh => ⟨maps h hh.1, (translated h hh.1).2 hh.2⟩)
        (fun h hh => fix h hh.1) hr⟩
    · exact Or.inr ⟨β, hβ, ih β hβ (J := J ⊓ MulAction.stabilizer K y)
        (fun h hh => ⟨maps h hh.1, (fix h hh.1).2 hh.2⟩)
        (fun h hh => translated h hh.1) hr⟩

theorem ComparisonLE.restrict {α : Ordinal.{w}} {H J : Subgroup G} {x : X}
    (h : H ≤ J) (rank : ComparisonLE α J x) : ComparisonLE α H x :=
  rank.of_hom (MonoidHom.id G) (fun _ hg => h hg) (fun _ _ => Iff.rfl)

/-- The comparison rank of a point is determined by its stabilizer in the current subgroup. -/
theorem ComparisonLE.of_stabilizer {α : Ordinal.{w}} {H : Subgroup G} {x : X} {Z : Type*}
    [MulAction G Z] {y : Z} (fix : ∀ g ∈ H, g • y = y ↔ g • x = x)
    (rank : ComparisonLE α H y) : ComparisonLE α H x :=
  rank.of_hom (MonoidHom.id G) (fun _ h => h) fix

theorem ComparisonLE.mono {α β : Ordinal.{w}} {H : Subgroup G} {x : X}
    (h : α ≤ β) (rank : ComparisonLE α H x) : ComparisonLE β H x := by
  rcases h.eq_or_lt with rfl | h
  · exact rank
  rw [comparisonLE_iff_of_ne_zero (ne_of_gt (lt_of_le_of_lt (zero_le : 0 ≤ α) h))]
  exact fun _ _ => Or.inl ⟨α, h, rank.restrict inf_le_left⟩

theorem ComparisonLE.translate {α : Ordinal.{w}} {H : Subgroup G} {x : X}
    (rank : ComparisonLE α H x) (g : G) (hg : g ∈ H) : ComparisonLE α H (g • x) :=
  rank.of_hom (MulAut.conj g⁻¹).toMonoidHom
    (fun h hh => by simpa using H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
    (fun h _ => by simpa using (fixes_translate_iff g h x).symm)

/-- Stabilizer of every entry of a finite parameter set. -/
def setStabilizer (G : Type*) [Group G] [MulAction G X] (B : Finset X) : Subgroup G where
  carrier := {g | ∀ x ∈ B, g • x = x}
  one_mem' := fun _ _ => one_smul _ _
  mul_mem' := fun ha hb x hx => by rw [mul_smul, hb x hx, ha x hx]
  inv_mem' := fun {g} hg x hx => by simpa using (congrArg (g⁻¹ • ·) (hg x hx)).symm

theorem setStabilizer_insert [DecidableEq X] (x : X) (B : Finset X) :
    setStabilizer G (insert x B) = setStabilizer G B ⊓ MulAction.stabilizer G x := by
  ext g
  change (∀ y ∈ insert x B, g • y = y) ↔ (∀ y ∈ B, g • y = y) ∧ g • x = x
  simp [and_comm]

/-- Comparison-only bounds imply the corresponding original rank bound. -/
theorem ComparisonLE.ordinalRankLE [DecidableEq X] {α : Ordinal.{w}} {B : Finset X} {x : X}
    (rank : ComparisonLE α (setStabilizer G B) x) : RankTwo.OrdinalRankLE G α B x := by
  induction α using WellFoundedLT.induction generalizing B x with
  | ind α ih =>
    rw [RankTwo.OrdinalRankLE]
    by_cases h : α = 0
    · subst α
      rw [if_pos rfl]
      exact (comparisonLE_zero ..).1 rank
    rw [if_neg h]
    apply Or.inr
    rintro y ⟨g, hg, rfl⟩
    rcases (comparisonLE_iff_of_ne_zero h ..).1 rank g hg with ⟨β, hb, hr⟩ | ⟨β, hb, hr⟩
    · exact Or.inl ⟨β, hb, ih β hb (by rwa [setStabilizer_insert])⟩
    · exact Or.inr ⟨β, hb, ih β hb (by rwa [setStabilizer_insert])⟩

end KnightModel.Transfinite
