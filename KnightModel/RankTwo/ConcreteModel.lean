import KnightModel.RankTwo.AtlasSize
import KnightModel.RankTwo.BaseLanguage

/-! # The named three-sorted structures

A transition name is a parameter-free word scheme of its declared arity.
An instance is defined exactly when all the base arguments are nonnegative
vectors and its graph describes a full initial coordinate. Both structures
interpret precisely the same names by the same rule.
-/

namespace KnightModel.RankTwo.Concrete

open Cardinal Set Scott

/-- The arity is part of the relation symbol, independently of the index model. -/
abbrev Name (n : ℕ) := {k : WordScheme // k.arity = n}

noncomputable section

/-- The language has only countably many relation symbols across all arities. -/
instance {Ω : Type} [Countable Ω] : Countable (Σ n, FrameRelation (BaseRelation Ω) Name n) := by
  let decode : (Σ n, BaseRelation Ω n) ⊕ (Bool ⊕ WordScheme) →
      Σ n, FrameRelation (BaseRelation Ω) Name n
    | .inl ⟨_,r⟩ => ⟨_,.base r⟩
    | .inr (.inl false) => ⟨_,.frame⟩
    | .inr (.inl true) => ⟨_,.below⟩
    | .inr (.inr k) => ⟨_,.transition (⟨k,rfl⟩ : Name k.arity)⟩
  have surj : Function.Surjective decode := by
    rintro ⟨n,r⟩
    cases r with
    | base r => exact ⟨.inl ⟨_,r⟩,rfl⟩
    | frame => exact ⟨.inr (.inl false),rfl⟩
    | below => exact ⟨.inr (.inl true),rfl⟩
    | transition k =>
      obtain ⟨k,rfl⟩ := k
      exact ⟨.inr (.inr k),rfl⟩
  exact surj.countable

instance {Ω : Type} [Countable Ω] (n : Nat) : Countable (FrameRelation (BaseRelation Ω) Name n) :=
  (show Function.Injective (Sigma.mk n : FrameRelation (BaseRelation Ω) Name n → Σ m, _) from
    sigma_mk_injective).countable

section Coordinates
variable {I : Type} [LinearOrder I]

abbrev family (i : I) : CoordinateFamily (Word (Letter I)) :=
  schematicFamily Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter

abbrev Code (i : I) := (family i).Code

/-- Literal equality with the word graph of a particular parameter tuple. -/
def Graph {n : ℕ} (i : I) (k : Name n) (p : Fin n → Letter I) (c : Code i) : Prop :=
  ∀ x y, k.val.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter
    (List.ofFn p) x y ↔ c.val x = y

def Presents {n : ℕ} (i : I) (k : Name n) (t : Tuple (BasePoints I) n) (c : Code i) : Prop :=
  ∃ p : Fin n → Letter I, (∀ j, t j = Sum.inr (p j).val) ∧ Graph i k p c

theorem presents_unique {n : ℕ} {i : I} {k : Name n} {t : Tuple (BasePoints I) n}
    {c e : Code i} (hc : Presents i k t c) (he : Presents i k t e) : c = e := by
  obtain ⟨p,hp,hc⟩ := hc
  obtain ⟨q,hq,he⟩ := he
  obtain rfl : p = q := funext fun j => Subtype.ext (Sum.inr.inj ((hp j).symm.trans (hq j)))
  exact Subtype.ext (DFunLike.ext _ _ (fun x => ((he x _).mp ((hc x _).mpr rfl)).symm))

/-- A name with unsuitable arguments or a noncoordinate graph is undefined. -/
def run {n : ℕ} (i : I) (k : Name n) (t : Tuple (BasePoints I) n) : Option (Code i) := by
  classical
  exact if h : ∃ c, Presents i k t c then some h.choose else none

theorem run_eq_some {n : ℕ} {i : I} {k : Name n} {t : Tuple (BasePoints I) n} {c : Code i} :
    run i k t = some c ↔ Presents i k t c := by
  classical
  by_cases h : ∃ c, Presents i k t c
  · simp only [run, dif_pos h, Option.some.injEq]
    exact ⟨fun he => he ▸ h.choose_spec, fun hc => presents_unique h.choose_spec hc⟩
  · simp only [run, dif_neg h, reduceCtorEq, false_iff]
    exact fun hc => h ⟨c,hc⟩

/-- For actual letter arguments the parameter fiber is exactly extensional
equality of the scheme graph with the fixed coordinate. -/
theorem run_letters_iff {n : ℕ} (i : I) (k : Name n) (p : Fin n → Letter I) (c : Code i) :
    run i k (fun j => Sum.inr (p j).val) = some c ↔ Graph i k p c := by
  rw [run_eq_some]
  constructor
  · rintro ⟨q,hq,h⟩
    obtain rfl : p = q := funext fun j => Subtype.ext (Sum.inr.inj (hq j))
    exact h
  · exact fun h => ⟨p,fun _ => rfl,h⟩

/-- Validity can be tested on the interpreted word relation without a
previously chosen coordinate or a presentation of that coordinate. -/
theorem run_exists_iff {n : ℕ} (i : I) (k : Name n) (p : Fin n → Letter I) :
    (∃ c, run i k (fun j => Sum.inr (p j).val) = some c) ↔
    ∃ e : Word (Letter I) ↪o Word (Letter I), CoordinateFamily.FullInitial e ∧
      ∀ x y, k.val.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i)
        Word.shiftOpenLetter (List.ofFn p) x y ↔ e x = y := by
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c.val,c.property.2,(run_letters_iff i k p c).mp hc⟩
  · rintro ⟨e,he,hg⟩
    let c : Code i := ⟨e,⟨k.val,List.ofFn p,(List.length_ofFn.trans k.property.symm),hg⟩,he⟩
    exact ⟨c,(run_letters_iff i k p c).mpr hg⟩

/-- A code has proper image exactly when its graph omits a target word. -/
theorem proper_iff_gap {i : I} (c : Code i) :
    c.val ⊤ < ⊤ ↔ ∃ z, ∀ x, c.val x ≠ z := by
  constructor
  · intro h
    refine ⟨⊤,fun x hx => ?_⟩
    have hle : c.val x ≤ c.val ⊤ := c.val.monotone le_top
    rw [hx] at hle
    exact (not_le_of_gt h) hle
  · rintro ⟨z,h⟩
    apply lt_of_le_of_ne le_top
    intro he
    have hz : z ∈ Set.range c.val := by
      rw [c.property.2]
      change z ≤ c.val ⊤
      rw [he]
      exact le_top
    obtain ⟨x,hx⟩ := hz
    exact h x hx

/-- Every allowed concrete coordinate occurs among the named, parameterized maps. -/
theorem run_covers (i : I) (c : Code i) :
    ∃ (n : ℕ) (k : Name n) (t : Tuple (BasePoints I) n), run i k t = some c := by
  obtain ⟨k,p,hp,h⟩ := c.property.1
  refine ⟨p.length, ⟨k,hp.symm⟩, fun j => Sum.inr (p.get j).val,
    (run_letters_iff _ _ _ _).mpr ?_⟩
  simpa only [Graph,List.ofFn_get] using h

/-- Coverage in the vector-only format used by the rank argument. -/
theorem run_covers_vectors (i : I) (c : Code i) :
    ∃ (n : ℕ) (k : Name n) (v : Fin n → VectorGroup I), run i k (Sum.inr ∘ v) = some c := by
  obtain ⟨n,k,t,ht⟩ := run_covers i c
  obtain ⟨p,_,h⟩ := run_eq_some.mp ht
  exact ⟨n,k,fun j => (p j).val,(run_letters_iff _ _ _ _).mpr h⟩

abbrev SmallFrames (i : I) := (family i).ProperFrames

abbrev smallAction (i : I) : FrameAction (Code i) (SmallFrames i) := by
  letI : Nonempty I := ⟨i⟩
  exact smallFrameAction Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter

end Coordinates

variable {Ω I : Type} [Blueprint Ω] [KnightModel I Ω]

/-- The countable-side interpretation uses proper charts in the word order with its root deleted. -/
def smallInterpretation (i : I) : FrameInterpretation (BaseRelation Ω) Name (BasePoints I) (smallAction i) where
  base := baseModel i
  run := run i
  faithful f _ _ h := Subtype.ext (DFunLike.ext _ _ (fun w => f.val.val.injective
    (congrArg (fun g : SmallFrames i => g.val.val w) h)))

abbrev SmallCarrier (I : Type) [LinearOrder I] (i : I) :=
  BasePoints I ⊕ SmallFrames i

def smallModel (i : I) : Model (FrameRelation (BaseRelation Ω) Name) (SmallCarrier I i) :=
  (smallInterpretation i).model

theorem countable_small [Nonempty I] [Countable I] (i : I) : Countable (SmallCarrier I i) :=
  countable_small_carrier i

variable [Nonempty I]

abbrev LargeFrames (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :=
  (knightLadders (Ω := Ω) S unc).markedRows.Frames (knightTransports (Ω := Ω) S unc i) (family i)

local instance : NoMaxOrder OuterIndex := Cardinal.noMaxOrder (aleph0_le_aleph 2)

abbrev largeAction (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :
    FrameAction (Code i) (LargeFrames (Ω := Ω) S unc i) :=
  (knightLadders (Ω := Ω) S unc).largeFrameAction Word.shiftLetter ⟨0,le_rfl⟩
    (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter

def largeInterpretation (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :
    FrameInterpretation (BaseRelation Ω) Name (BasePoints I) (largeAction (Ω := Ω) S unc i) where
  base := baseModel i
  run := run i
  faithful f _ _ h := Subtype.ext (DFunLike.ext _ _ (fun w => f.val.injective
    (congrArg (fun g : LargeFrames (Ω := Ω) S unc i => g.val w) h)))

abbrev LargeCarrier (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :=
  BasePoints I ⊕ LargeFrames (Ω := Ω) S unc i

def largeModel (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :
    Model (FrameRelation (BaseRelation Ω) Name) (LargeCarrier (Ω := Ω) S unc i) :=
  (largeInterpretation (Ω := Ω) S unc i).model

/-- The entire interpreted carrier, after adjoining both base sorts, has size ℵ₂. -/
theorem mk_large (S : SquareLadders OuterIndex (aleph 1).ord) (unc : ¬Countable I) (i : I) :
    #(LargeCarrier (Ω := Ω) S unc i) = aleph 2 := by
  have one_two : (aleph 1 : Cardinal) ≤ aleph 2 := aleph_le_aleph.mpr one_le_two
  have hI : #I ≤ aleph 2 := (KnightModel.knightModel_card_le_aleph_one (Ω := Ω)).trans one_two
  have hV : #(VectorGroup I) ≤ aleph 2 := (cardinal_vectorGroup_le_aleph_one (Ω := Ω)).trans one_two
  have hF : #(LargeFrames (Ω := Ω) S unc i) = aleph 2 := mk_knight_frames S unc i
  change #((I ⊕ VectorGroup I) ⊕ LargeFrames (Ω := Ω) S unc i) = aleph 2
  simp only [mk_sum, lift_id, hF]
  apply le_antisymm
  · calc
      #I + #(VectorGroup I) + aleph 2 ≤ aleph 2 + aleph 2 + aleph 2 :=
        add_le_add (add_le_add hI hV) le_rfl
      _ = aleph 2 := by rw [add_eq_self (aleph0_le_aleph 2), add_eq_self (aleph0_le_aleph 2)]
  · exact le_add_self

end
end KnightModel.RankTwo.Concrete
