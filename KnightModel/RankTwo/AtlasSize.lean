import KnightModel.RankTwo.AtlasFamily
import KnightModel.RankTwo.FrameCardinality
import KnightModel.RankTwo.AtlasKnight

/-! # Cardinality of the schematic coordinates and the two frame sorts -/

namespace KnightModel.RankTwo

open Cardinal Set

variable {A : Type} [LinearOrder A] (shift : ∀ a : A, Ici a ≃o A)
    (o d : A) (hd : o < d) (upper : ∀ a : A, Ioi a ≃o Ioi o)

private theorem coord_presentation (c : (schematicFamily shift o d hd upper).Code) :
    ∃ p : WordScheme × List A, ∀ x y, p.1.Rel shift o d hd upper p.2 x y ↔ c.val x = y := by
  obtain ⟨code,args,_,hp⟩ := c.property.1
  exact ⟨(code,args),hp⟩

/-- One presentation is enough to bound the cardinality of the extensional
coordinate algebra. Different coordinates cannot share a presentation. -/
noncomputable def coordEncoding :
    (schematicFamily shift o d hd upper).Code ↪ WordScheme × List A where
  toFun c := (coord_presentation shift o d hd upper c).choose
  inj' := by
    intro c e he
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    have hc := (coord_presentation shift o d hd upper c).choose_spec x (c.val x)
    have he' := (coord_presentation shift o d hd upper e).choose_spec x (c.val x)
    change (coord_presentation shift o d hd upper c).choose =
      (coord_presentation shift o d hd upper e).choose at he
    rw [he] at hc
    exact (he'.mp (hc.mpr rfl)).symm

theorem countable_schematic_code [Countable A] :
    Countable (schematicFamily shift o d hd upper).Code :=
  (coordEncoding shift o d hd upper).injective.countable

theorem countable_proper_frames [Countable A] :
    Countable (schematicFamily shift o d hd upper).ProperFrames := by
  letI := countable_schematic_code shift o d hd upper
  infer_instance

theorem mk_schematic_code (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hA : #(List A) ≤ κ) :
    #(schematicFamily shift o d hd upper).Code ≤ κ := calc
  _ ≤ #(WordScheme × List A) := mk_le_of_injective (coordEncoding shift o d hd upper).injective
  _ = #WordScheme * #(List A) := by simp [mk_prod]
  _ ≤ κ * κ := mul_le_mul' ((mk_le_aleph0_iff.mpr inferInstance).trans hκ) hA
  _ = κ := mul_eq_self hκ

variable {Ω I : Type} [Blueprint Ω] [KnightModel I Ω] [Nonempty I]

/-- A countable Knight index has only countably many vector parameters. -/
theorem countable_knight_vectors [Countable I] : Countable (VectorGroup I) := by
  apply mk_le_aleph0_iff.mp
  change #(I →₀ ℚ) ≤ ℵ₀
  rw [mk_finsupp_of_infinite', Cardinal.mkRat]
  exact max_le (mk_le_aleph0_iff.mpr inferInstance) le_rfl

theorem countable_knight_letters [Countable I] : Countable (Letter I) := by
  letI := countable_knight_vectors (I := I)
  infer_instance

/-- The actual countable model has countable carrier including all proper
schematic coordinates, as well as the index and vector sorts. -/
theorem countable_small_carrier [Countable I] (i : I) :
    Countable ((I ⊕ VectorGroup I) ⊕
      (schematicFamily Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i)
        Word.shiftOpenLetter).ProperFrames) := by
  letI := countable_knight_vectors (I := I)
  letI := countable_knight_letters (Ω := Ω) (I := I)
  letI := countable_proper_frames Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i)
    Word.shiftOpenLetter
  infer_instance

/-- The cardinal counts genuine distinct frames of the concrete vector-word
construction over an uncountable Knight model. -/
theorem mk_knight_frames (S : SquareLadders OuterIndex (aleph 1).ord)
    (hI : ¬ Countable I) (i : I) :
    let C := knightLadders (Ω := Ω) S hI
    let q : C.markedRows.Transports := knightTransports (Ω := Ω) S hI i
    let o : Letter I := ⟨0,le_rfl⟩
    #(C.markedRows.Frames q (schematicFamily Word.shiftLetter o (unitLetter i) (zero_lt_unit i)
      Word.shiftOpenLetter)) = aleph 2 := by
  intro C q o
  apply MarkedRows.cardinal_frames_omega_two
  exact (mk_schematic_code Word.shiftLetter o (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter
    (aleph 1) (aleph0_le_aleph 1) (cardinal_words_le_aleph_one (Ω := Ω))).trans
      (aleph_le_aleph.mpr one_le_two)

end KnightModel.RankTwo
