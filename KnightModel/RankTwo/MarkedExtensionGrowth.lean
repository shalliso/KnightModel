import KnightModel.RankTwo.MarkedExtensionStrict
import KnightModel.RankTwo.RestrictionTree

/-! # An ω₂-sized model from proper extensions of all models of size at most ℵ₁

At each stage take the elementary direct limit of all earlier models, then
choose a point outside its image in a small extension. The points chosen at
distinct stages remain distinct in the final direct limit.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal Restriction Set Transfinite

variable {R : ℕ → Type}

private structure GrowthStage (φ : Formula R 0) where
  world : World R
  sat : BackAndForth.Satisfies world.model φ
  small : #world.carrier ≤ ℵ₁
  point : world.carrier

namespace GrowthStage

variable {φ : Formula R 0}

private abbrev Hom (A B : GrowthStage φ) := Elementary A.world.model B.world.model

private abbrev comp {A B C : GrowthStage φ} (f : Hom A B) (g : Hom B C) : Hom A C :=
  f.comp g

private theorem hom_ext {A B : GrowthStage φ} {f g : Hom A B} (h : ∀ x, f x = g x) : f = g := by
  have eq : f.toEmbedding = g.toEmbedding := Function.Embedding.ext h
  cases f
  cases g
  cases eq
  rfl

private noncomputable def tower {I : Type} [LinearOrder I] (D : Diagram (Hom (φ := φ)) comp I) :
    Tower R I :=
  ofStrict D GrowthStage.world (fun f => f) (fun _ _ _ => rfl)

end GrowthStage

/-- The transfinite growth step in the marked-extension criterion. Every
small model admits an elementary extension of size at most ℵ₁ with
a new point. Starting with any one pointed small model produces a model of
size exactly ℵ₂. -/
theorem exists_aleph_two_of_small_extensions (φ : Formula R 0) (A : World R)
    (sat : BackAndForth.Satisfies A.model φ) (small : #A.carrier ≤ ℵ₁) (point : A.carrier)
    (extend : ∀ W : World R, BackAndForth.Satisfies W.model φ → #W.carrier ≤ ℵ₁ →
      ∃ (V : World R) (e : Elementary W.model V.model) (v : V.carrier),
        #V.carrier ≤ ℵ₁ ∧ ∀ x, e x ≠ v) :
    ∃ V : World R, #V.carrier = aleph 2 ∧ BackAndForth.Satisfies V.model φ := by
  classical
  let start : GrowthStage φ := ⟨A, sat, small, point⟩
  let P : StageProperty (GrowthStage.Hom (φ := φ)) (J := OmegaTwo) :=
    fun _ old new legs => ∀ i (x : (old i).world.carrier), legs i x ≠ new.point
  have step (j : OmegaTwo) (D : Diagram (GrowthStage.Hom (φ := φ)) GrowthStage.comp (Iio j)) :
      ∃ c : Apex _ _ D, P j D.obj c.obj c.leg := by
    rcases isEmpty_or_nonempty (Iio j) with he | hi
    · letI := he
      exact ⟨⟨start, fun i => isEmptyElim i, fun {i} => isEmptyElim i⟩, fun i => isEmptyElim i⟩
    · let T := GrowthStage.tower D
      let i := Classical.choice hi
      have hsize : #(Iio j) ≤ ℵ₁ := by
        apply Order.lt_succ_iff.mp
        simpa only [succ_aleph, one_add_one_eq_two, mk_toType, card_ord] using mk_Iio_lt j (by simp)
      obtain ⟨V, e, v, hv, fresh⟩ := extend T.limit
        (((T.into i).sentence φ).mp (D.obj i).sat)
        (T.mk_limit_le ℵ₁ (aleph0_le_aleph 1) hsize (fun k => (D.obj k).small))
      let X : GrowthStage φ := ⟨V, (e.sentence φ).mp (((T.into i).sentence φ).mp (D.obj i).sat), hv, v⟩
      let leg (k : Iio j) : GrowthStage.Hom (D.obj k) X := (T.into k).comp e
      refine ⟨⟨X, leg, ?_⟩, fun k x => fresh (T.into k x)⟩
      intro k l h
      apply GrowthStage.hom_ext
      intro x
      apply congrArg e
      change T.into l (D.map h x) = T.into k x
      exact ofStrict_into_map_lt D GrowthStage.world (fun f => f) (fun _ _ _ => rfl) h x
  obtain ⟨D, fresh⟩ := Transfinite.build (GrowthStage.Hom (φ := φ)) GrowthStage.comp start P step
  let T := GrowthStage.tower D
  let f (i : OmegaTwo) := T.into i (D.obj i).point
  have inj : Function.Injective f := ofStrict_fresh_injective D GrowthStage.world
    (fun g => g) (fun _ _ _ => rfl) (fun i => (D.obj i).point) (fun i j h => fresh j ⟨i, h⟩)
  have hcard : #OmegaTwo = aleph 2 := by simp only [mk_toType, card_ord]
  have oneTwo : ℵ₁ ≤ aleph.{0} 2 := aleph_le_aleph.mpr _root_.one_lt_two.le
  have lower : aleph 2 ≤ #T.limit.carrier := hcard.ge.trans (mk_le_of_injective inj)
  let i : OmegaTwo := Ordinal.ToType.mk ⟨0, ord_pos.mpr (aleph_pos 2)⟩
  exact ⟨T.limit, (T.mk_limit_le _ (aleph0_le_aleph 2) hcard.le fun j =>
    (D.obj j).small.trans oneTwo).antisymm lower,
    ((T.into i).sentence φ).mp (D.obj i).sat⟩

end KnightModel.RankTwo.Scott.MarkedExtension
