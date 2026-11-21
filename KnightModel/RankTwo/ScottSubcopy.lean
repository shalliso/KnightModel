import KnightModel.RankTwo.AmalgamationScott
import Mathlib.Data.Set.Countable

/-! # Countable elementary copies in arbitrary models of a Scott sentence

At each stage choose one witness for each realized finite extension label over
the previous stage. Every finite tuple in the union is contained in one
stage. Its extension witnesses suffice for the entire infinitary language.
-/

namespace KnightModel.RankTwo.Scott

open Set

variable {R : ℕ → Type} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

def inducedModel (E : Model R N) (S : Set N) : Model R S :=
  fun r t => E r (Subtype.val ∘ t)

/-- Contains representatives of every one-point extension type over its finite tuples. -/
def LabelClosed (S : Set N) : Prop := ∀ {n} (t : Tuple N n), (∀ i, t i ∈ S) → ∀ y : N,
  ∃ x ∈ S, SentenceLabels.number C D E sat (push x t) = SentenceLabels.number C D E sat (push y t)

namespace LabelClosed

private abbrev Test (S : Set N) := (n : ℕ) × Tuple S n × ℕ

private def realized (S : Set N) (v : Test S) : Prop :=
  ∃ y, SentenceLabels.number C D E sat (push y (Subtype.val ∘ v.2.1)) = v.2.2

private noncomputable def witness (S : Set N) (p : {v : Test S // realized C sat S v}) : N :=
  p.property.choose

private def step (S : Set N) : Set N := S ∪ range (witness C sat S)

private theorem step_small (S : Set N) (small : S.Countable) : (step C sat S).Countable := by
  haveI : Countable S := small
  exact small.union (countable_range _)

private def stages (A : Set N) : Nat → Set N
  | 0 => A
  | n+1 => step C sat (stages A n)

private theorem stages_mono (A : Set N) : Monotone (stages C sat A) :=
  monotone_nat_of_le_succ (fun _ _ h => Or.inl h)

private theorem stages_small {A : Set N} (small : A.Countable) (k : Nat) :
    (stages C sat A k).Countable := by
  induction k with
  | zero => exact small
  | succ _ ih => exact step_small C sat _ ih

private theorem stage_of_tuple (A : Set N) {n} (t : Tuple N n)
    (mem : ∀ i, t i ∈ ⋃ k, stages C sat A k) : ∃ k, ∀ i, t i ∈ stages C sat A k := by
  induction n with
  | zero => exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨k,hk⟩ := mem_iUnion.mp (mem 0)
    obtain ⟨l,hl⟩ := ih (fun i => t i.succ) (fun i => mem i.succ)
    exact ⟨max k l, Fin.cases (stages_mono C sat A (le_max_left _ _) hk)
      (fun i => stages_mono C sat A (le_max_right _ _) (hl i))⟩

private theorem hull_countable_data {A : Set N} (small : A.Countable) :
    A ⊆ ⋃ k, stages C sat A k ∧ (⋃ k, stages C sat A k).Countable ∧ LabelClosed C sat (⋃ k, stages C sat A k) := by
  refine ⟨fun y hy => mem_iUnion.mpr ⟨0,hy⟩, countable_iUnion (stages_small C sat small), ?_⟩
  intro n t mem y
  obtain ⟨k,hk⟩ := stage_of_tuple C sat A t mem
  let v : Test (stages C sat A k) := ⟨n, fun i => ⟨t i,hk i⟩,
    SentenceLabels.number C D E sat (push y t)⟩
  have r : realized C sat _ v := ⟨y,rfl⟩
  let w := witness C sat _ ⟨v,r⟩
  refine ⟨w,mem_iUnion.mpr ⟨k+1,?_⟩,r.choose_spec⟩
  exact Or.inr ⟨⟨v,r⟩,rfl⟩

/-- A fixed choice of extension witnesses gives a monotone Skolem hull. -/
def hull (A : Set N) : Set N := ⋃ k, stages C sat A k

theorem hull_small {A : Set N} (small : A.Countable) : (hull C sat A).Countable :=
  (hull_countable_data C sat small).2.1

theorem hull_closed {A : Set N} (small : A.Countable) : LabelClosed C sat (hull C sat A) :=
  (hull_countable_data C sat small).2.2

theorem subset_hull (A : Set N) : A ⊆ hull C sat A := fun _ h => mem_iUnion.mpr ⟨0,h⟩

theorem exists_countable {A : Set N} (small : A.Countable) :
    ∃ S : Set N, A ⊆ S ∧ S.Countable ∧ LabelClosed C sat S :=
  ⟨hull C sat A,subset_hull C sat A,hull_small C sat small,hull_closed C sat small⟩

private theorem tuple_bounded {I : Type} [Nonempty I] (U : I → Set N) (dir : Directed (· ⊆ ·) U)
    {n} (t : Tuple N n) (mem : ∀ l, t l ∈ ⋃ j, U j) : ∃ j, ∀ l, t l ∈ U j := by
  induction n with
  | zero => exact ⟨Classical.choice inferInstance,fun l => l.elim0⟩
  | succ n ih =>
    obtain ⟨i,hi⟩ := mem_iUnion.mp (mem 0)
    obtain ⟨j,hj⟩ := ih (fun l => t l.succ) (fun l => mem l.succ)
    obtain ⟨k,ik,jk⟩ := dir i j
    exact ⟨k,Fin.cases (ik hi) (fun l => jk (hj l))⟩

/-- A directed union of elementary Scott copies in the same model is again elementary. -/
theorem iUnion_directed {I : Type} [Nonempty I] (U : I → Set N) (dir : Directed (· ⊆ ·) U)
    (closed : ∀ i, LabelClosed C sat (U i)) : LabelClosed C sat (⋃ i, U i) := by
  intro n t mem y
  obtain ⟨i,hi⟩ := tuple_bounded U dir t mem
  obtain ⟨x,hx,h⟩ := closed i t hi y
  exact ⟨x,mem_iUnion.mpr ⟨i,hx⟩,h⟩

private theorem step_mono {A B : Set N} (sub : A ⊆ B) : step C sat A ⊆ step C sat B := by
  rintro x (hx | ⟨⟨⟨n,t,k⟩,r⟩,rfl⟩)
  · exact Or.inl (sub hx)
  · exact Or.inr ⟨⟨⟨n,fun l => ⟨(t l).val,sub (t l).property⟩,k⟩,r⟩,rfl⟩

private theorem stages_inclusion {A B : Set N} (sub : A ⊆ B) (k : Nat) :
    stages C sat A k ⊆ stages C sat B k := by
  induction k with
  | zero => exact sub
  | succ k ih => exact step_mono C sat ih

theorem hull_mono {A B : Set N} (sub : A ⊆ B) : hull C sat A ⊆ hull C sat B :=
  iUnion_mono fun k => stages_inclusion C sat sub k

private theorem step_iUnion {I : Type} [Nonempty I] (U : I → Set N) (dir : Directed (· ⊆ ·) U) :
    step C sat (⋃ i, U i) = ⋃ i, step C sat (U i) := by
  apply Subset.antisymm _ (iUnion_subset fun i => step_mono C sat (subset_iUnion _ i))
  rintro x (hx | ⟨⟨⟨n,t,k⟩,r⟩,rfl⟩)
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,Or.inl hi⟩
  · obtain ⟨i,hi⟩ := tuple_bounded U dir (Subtype.val ∘ t) (fun l => (t l).property)
    exact mem_iUnion.mpr ⟨i,Or.inr ⟨⟨⟨n,fun l => ⟨(t l).val,hi l⟩,k⟩,r⟩,rfl⟩⟩

/-- Finitary witness selection makes the hull commute with directed unions. -/
theorem hull_iUnion {I : Type} [Nonempty I] (U : I → Set N) (dir : Directed (· ⊆ ·) U) :
    hull C sat (⋃ i, U i) = ⋃ i, hull C sat (U i) := by
  have stages_eq k : stages C sat (⋃ i, U i) k = ⋃ i, stages C sat (U i) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change step C sat (stages C sat _ k) = ⋃ i, step C sat (stages C sat (U i) k)
      rw [ih]
      apply step_iUnion
      intro i j
      obtain ⟨l,il,jl⟩ := dir i j
      exact ⟨l,stages_inclusion C sat il k,stages_inclusion C sat jl k⟩
  ext x
  simp only [hull,mem_iUnion,stages_eq]
  exact exists_comm

def system {S : Set N} (H : LabelClosed C sat S) : BackAndForth (inducedModel E S) E where
  matchTuples s t := SentenceLabels.number C D E sat (Subtype.val ∘ s) = SentenceLabels.number C D E sat t
  atoms := by
    intro n s t h a
    have same := (SentenceLabels.number_eq_iff C D E sat _ _).mp h (.atom a)
    cases a with
    | eq i j =>
      exact Subtype.ext_iff.trans same
    | rel r vars => exact same
  forth := by
    intro n s t h x
    obtain ⟨y,hy⟩ := SentenceLabels.number_extend C D E sat h x.val
    have comm : Subtype.val ∘ push x s = push x.val (Subtype.val ∘ s) :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact ⟨y,comm ▸ hy⟩
  back := by
    intro n s t h y
    obtain ⟨v,hv⟩ := SentenceLabels.number_extend C D E sat h.symm y
    obtain ⟨x,hx,he⟩ := H (Subtype.val ∘ s) (fun i => (s i).property) v
    have comm : Subtype.val ∘ push (⟨x,hx⟩ : S) s = push x (Subtype.val ∘ s) :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact ⟨⟨x,hx⟩,comm ▸ (he.trans hv.symm)⟩

/-- The elementary embedding is literally inclusion in the ambient Scott model. -/
def elementary {S : Set N} (H : LabelClosed C sat S) :
    MarkedExtension.Elementary (inducedModel E S) E where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  truth φ t := (system C sat H).holds_iff φ (s := t) (t := Subtype.val ∘ t) rfl

theorem satisfies {S : Set N} (H : LabelClosed C sat S) :
    BackAndForth.Satisfies (inducedModel E S) (C.sentence D) := by
  apply ((elementary C sat H).truth _ Fin.elim0).mpr
  change (C.sentence D).Holds E (Subtype.val ∘ (Fin.elim0 : Tuple S 0))
  rw [show Subtype.val ∘ (Fin.elim0 : Tuple S 0) = Fin.elim0 from Subsingleton.elim _ _]
  exact sat

/-- Between two such copies, any inclusion of the underlying sets is elementary. -/
def inclusion {S T : Set N} (H : LabelClosed C sat S) (K : LabelClosed C sat T) (sub : S ⊆ T) :
    MarkedExtension.Elementary (inducedModel E S) (inducedModel E T) where
  toFun x := ⟨x.val,sub x.property⟩
  inj' _ _ e := Subtype.ext (congrArg (fun y : T => y.val) e)
  truth φ t := ((elementary C sat H).truth φ t).trans ((elementary C sat K).truth φ
    (fun i => ⟨(t i).val,sub (t i).property⟩)).symm

end LabelClosed
namespace RelIso
variable {X Y : Type} {U : Model R X} {V : Model R Y}

/-- An isomorphism in the relational language preserves every infinitary formula. -/
def elementary (f : RelIso U V) : MarkedExtension.Elementary U V where
  toFun := f.toFun
  inj' := Function.LeftInverse.injective f.leftInv
  truth := by
    intro n φ t
    induction φ with
    | top => rfl
    | atom a =>
      cases a with
      | eq i j => exact (Function.LeftInverse.injective f.leftInv).eq_iff.symm
      | rel r vars => exact f.map_rel r (t ∘ vars)
    | neg φ ih => exact not_congr (ih t)
    | conj φs ih => exact forall_congr' (fun i => ih i t)
    | ex φ ih =>
      have comm (x : X) : f.toFun ∘ push x t = push (f.toFun x) (f.toFun ∘ t) :=
        funext (Fin.cases rfl (fun _ => rfl))
      constructor
      · rintro ⟨x,h⟩
        exact ⟨f.toFun x,comm x ▸ (ih _).mp h⟩
      · rintro ⟨y,h⟩
        refine ⟨f.invFun y,(ih _).mpr ?_⟩
        rwa [comm,f.rightInv]

def elementaryInverse (f : RelIso U V) : MarkedExtension.Elementary V U where
  toFun := f.invFun
  inj' := Function.LeftInverse.injective f.rightInv
  truth φ t := by
    have h := (f.elementary.truth φ (f.invFun ∘ t)).symm
    have e : f.toFun ∘ (f.invFun ∘ t) = t := funext fun i => f.rightInv (t i)
    change φ.Holds V (f.toFun ∘ (f.invFun ∘ t)) ↔ _ at h
    rwa [e] at h

end RelIso

namespace MarkedExtension.Elementary
variable {X Y Z : Type} {U : Model R X} {V : Model R Y} {W : Model R Z}

def comp (f : MarkedExtension.Elementary U V) (g : MarkedExtension.Elementary V W) :
    MarkedExtension.Elementary U W where
  toFun := g ∘ f
  inj' := g.toEmbedding.injective.comp f.toEmbedding.injective
  truth φ t := (f.truth φ t).trans (g.truth φ (f ∘ t))

end MarkedExtension.Elementary
end KnightModel.RankTwo.Scott
