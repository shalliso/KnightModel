import KnightModel.RankTwo.ScottSubcopy
import KnightModel.RankTwo.RestrictionOrdinal

/-! # Continuous ω₁-resolutions of small Scott models -/

namespace KnightModel.RankTwo.Scott.LabelClosed

open Cardinal Set Restriction

variable {R : ℕ → Type} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

/-- Literal countable elementary submodels exhausting the ambient model. -/
structure Resolution where
  level : OmegaOne → Set N
  small : ∀ i, (level i).Countable
  closed : ∀ i, LabelClosed C sat (level i)
  mono : Monotone level
  exhaustive : ∀ x, ∃ i, x ∈ level i
  continuous : ∀ i, (∃ j, j < i) → (∀ j, j < i → ∃ k, j < k ∧ k < i) →
    level i = ⋃ j : Iio i, level j.val

local instance : NoMaxOrder OmegaOne := Cardinal.noMaxOrder (aleph0_le_aleph 1)

/-- Take hulls of the open initial sections of an injection into ω₁. At
limit indices the directed-union theorem gives actual continuity. -/
noncomputable def resolution (size : #N ≤ ℵ₁) : Resolution C sat := by
  have emb : #N ≤ #OmegaOne := by simpa only [mk_toType,card_ord] using size
  let f := Classical.choice ((le_def N OmegaOne).mp emb)
  let A (i : OmegaOne) : Set N := f ⁻¹' Iio i
  have small i : (A i).Countable := by
    have hs : (Iio i).Countable := le_aleph0_iff_set_countable.mp <| lt_aleph_one_iff.mp
      (by simpa only [mk_toType,card_ord] using mk_Iio_lt i (by simp))
    exact hs.preimage f.injective
  have mono : Monotone A := fun _ _ ij _ hx => lt_of_lt_of_le hx ij
  refine {
    level := fun i => hull C sat (A i)
    small := fun i => hull_small C sat (small i)
    closed := fun i => hull_closed C sat (small i)
    mono := fun _ _ h => hull_mono C sat (mono h)
    exhaustive := ?_
    continuous := ?_ }
  · intro x
    obtain ⟨i,hi⟩ := exists_gt (f x)
    exact ⟨i,subset_hull C sat _ hi⟩
  · intro i nonempty between
    haveI : Nonempty (Iio i) := by obtain ⟨j,hj⟩ := nonempty; exact ⟨⟨j,hj⟩⟩
    have eq : A i = ⋃ j : Iio i, A j.val := by
      apply Subset.antisymm _ (iUnion_subset (fun j => mono j.property.le))
      intro x hx
      obtain ⟨k,hk,ki⟩ := between (f x) hx
      exact mem_iUnion.mpr ⟨⟨k,ki⟩,hk⟩
    have dir : Directed (· ⊆ ·) (fun j : Iio i => A j.val) := fun j k =>
      match le_total j.val k.val with
      | .inl h => ⟨k,mono h,Subset.rfl⟩
      | .inr h => ⟨j,Subset.rfl,mono h⟩
    exact (congrArg (hull C sat) eq).trans (hull_iUnion C sat _ dir)

namespace Resolution
variable {C sat} (L : Resolution C sat)

/-- Transition embeddings are the canonical subtype inclusions. -/
def embed {i j : OmegaOne} (h : i ≤ j) :
    MarkedExtension.Elementary (inducedModel E (L.level i)) (inducedModel E (L.level j)) :=
  inclusion C sat (L.closed i) (L.closed j) (L.mono h)

@[simp] theorem embed_val {i j : OmegaOne} (h : i ≤ j) (x : L.level i) : (L.embed h x).val = x.val := rfl

@[simp] theorem embed_self {i : OmegaOne} (x : L.level i) : L.embed le_rfl x = x := rfl

@[simp] theorem embed_embed {i j k : OmegaOne} (ij : i ≤ j) (jk : j ≤ k) (x : L.level i) :
    L.embed jk (L.embed ij x) = L.embed (ij.trans jk) x := rfl

theorem satisfies (i : OmegaOne) : BackAndForth.Satisfies (inducedModel E (L.level i)) (C.sentence D) :=
  LabelClosed.satisfies C sat (L.closed i)

end Resolution
end KnightModel.RankTwo.Scott.LabelClosed
