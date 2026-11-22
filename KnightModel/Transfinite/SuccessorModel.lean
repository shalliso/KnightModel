import KnightModel.Transfinite.Atlas
import KnightModel.RankTwo.ScottCountable

/-! # The actual successor structures over an arbitrary ordered old model -/

namespace KnightModel.Transfinite

open RankTwo Scott Cardinal

/-- Retain every old relation and name the rational coefficients of each finite vector. -/
inductive BaseRelation (R : ℕ → Type) : ℕ → Type where
  | old {n} (r : R n) : BaseRelation R n
  | indexSort : BaseRelation R 1
  | vectorSort : BaseRelation R 1
  | coefficient (q : ℚ) : BaseRelation R 2

variable {R : ℕ → Type} {I : Type} [LinearOrder I]

def baseModel (D : Scott.Model R I) : Scott.Model (BaseRelation R) (Scott.BasePoints I)
  | _, .old r, s => ∃ t, (∀ j, s j = .inl (t j)) ∧ D r t
  | _, .indexSort, s => ∃ x : I, s 0 = .inl x
  | _, .vectorSort, s => ∃ v : VectorGroup I, s 0 = .inr v
  | _, .coefficient q, s => ∃ (v : VectorGroup I) (x : I),
      s 0 = .inr v ∧ s 1 = .inl x ∧ v x = q

/-- The word-scheme relations are unchanged at all successor stages. -/
abbrev SuccessorRelation (R : ℕ → Type) := FrameRelation (BaseRelation R) Concrete.Name

instance [Countable (Σ n, R n)] : Countable (Σ n, SuccessorRelation R n) := by
  let dec : ((Σ n, R n) ⊕ (Bool ⊕ ℚ)) ⊕ (Bool ⊕ WordScheme) → Σ n, SuccessorRelation R n
    | .inl (.inl ⟨_,r⟩) => ⟨_,.base (.old r)⟩
    | .inl (.inr (.inl false)) => ⟨_,.base .indexSort⟩
    | .inl (.inr (.inl true)) => ⟨_,.base .vectorSort⟩
    | .inl (.inr (.inr q)) => ⟨_,.base (.coefficient q)⟩
    | .inr (.inl false) => ⟨_,.frame⟩
    | .inr (.inl true) => ⟨_,.below⟩
    | .inr (.inr k) => ⟨_,.transition (⟨k,rfl⟩ : Concrete.Name k.arity)⟩
  have hs : Function.Surjective dec := by
    rintro ⟨n,r⟩
    cases r with
    | base r =>
      cases r with
      | old r => exact ⟨.inl (.inl ⟨_,r⟩),rfl⟩
      | indexSort => exact ⟨.inl (.inr (.inl false)),rfl⟩
      | vectorSort => exact ⟨.inl (.inr (.inl true)),rfl⟩
      | coefficient q => exact ⟨.inl (.inr (.inr q)),rfl⟩
    | frame => exact ⟨.inr (.inl false),rfl⟩
    | below => exact ⟨.inr (.inl true),rfl⟩
    | transition k =>
      obtain ⟨k,rfl⟩ := k
      exact ⟨.inr (.inr k),rfl⟩
  exact hs.countable

instance [Countable (Σ n, R n)] (n : ℕ) : Countable (SuccessorRelation R n) :=
  (show Function.Injective (Sigma.mk n : SuccessorRelation R n → Σ m, _) from sigma_mk_injective).countable

noncomputable section

def smallInterpretation (D : Scott.Model R I) (i : I) :
    FrameInterpretation (BaseRelation R) Concrete.Name (Scott.BasePoints I) (Concrete.smallAction i) where
  base := baseModel D
  run := Concrete.run i
  faithful f _ _ h := Subtype.ext (DFunLike.ext _ _ (fun w => f.val.val.injective
    (congrArg (fun g : Concrete.SmallFrames i => g.val.val w) h)))

abbrev SmallCarrier (i : I) := Concrete.SmallCarrier I i

def smallModel (D : Scott.Model R I) (i : I) : Scott.Model (SuccessorRelation R) (SmallCarrier i) :=
  (smallInterpretation D i).model

/-- The old base, new vector sort and countable proper frame sort together are countable. -/
theorem countable_smallCarrier [Countable I] (i : I) : Countable (SmallCarrier i) := by
  haveI : Countable (VectorGroup I) := mk_le_aleph0_iff.mp (mk_vector_le i le_rfl mk_le_aleph0)
  haveI : Countable (Letter I) := inferInstanceAs (Countable (Set.Ici (0 : VectorGroup I)))
  haveI : Countable (Concrete.SmallFrames i) := countable_proper_frames _ _ _ _ _
  exact inferInstanceAs (Countable ((I ⊕ VectorGroup I) ⊕ Concrete.SmallFrames i))

def largeInterpretation (D : Scott.Model R I) (i : I) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I) :
    FrameInterpretation (BaseRelation R) Concrete.Name (Scott.BasePoints I) (largeAction i κ hκ S slots) where
  base := baseModel D
  run := Concrete.run i
  faithful f _ _ h := Subtype.ext (DFunLike.ext _ _ (fun w => f.val.injective
    (congrArg (fun g : LargeFrames i κ S slots => g.val w) h)))

abbrev LargeCarrier (i : I) (κ : Cardinal.{0}) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o I) := Scott.BasePoints I ⊕ LargeFrames i κ S slots

def largeModel (D : Scott.Model R I) (i : I) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I) :
    Scott.Model (SuccessorRelation R) (LargeCarrier i κ S slots) :=
  (largeInterpretation D i κ hκ S slots).model

theorem mk_largeCarrier (i : I) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I)
    (hI : #I ≤ κ) : #(LargeCarrier i κ S slots) = Order.succ κ := by
  have hi := hI.trans (Order.le_succ κ)
  have hv := (mk_vector_le i hκ hI).trans (Order.le_succ κ)
  change #((I ⊕ VectorGroup I) ⊕ LargeFrames i κ S slots) = Order.succ κ
  simp only [mk_sum,lift_id,mk_largeFrames i κ hκ S slots hI]
  refine le_antisymm ((add_le_add (add_le_add hi hv) le_rfl).trans_eq ?_) le_add_self
  rw [add_eq_self (hκ.trans (Order.le_succ κ)),add_eq_self (hκ.trans (Order.le_succ κ))]

def smallPresentation [Countable (Σ n, R n)] [Countable I] (i : I) :
    Presentation (SuccessorRelation R) (SmallCarrier i) := by
  letI := countable_smallCarrier i
  let w := Word.cons (unitLetter i) Word.root
  let f := throughCode Word.shiftLetter (⟨0,le_rfl⟩ : Letter I) (unitLetter i)
    (zero_lt_unit i) Word.shiftOpenLetter w
  letI : Nonempty (SmallCarrier i) := ⟨.inl (.inl i)⟩
  exact Presentation.ofCountable _ _

end
end KnightModel.Transfinite
