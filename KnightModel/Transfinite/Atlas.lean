import KnightModel.RankTwo.ConcreteModel
import KnightModel.RankTwo.WalkSquareLimit

/-! # The word atlas at the successor of an arbitrary infinite cardinal

The increasing sequence in the old ordered index labels the positions in
the square sequence. No regularity of the old cardinal is required.
-/

namespace KnightModel.Transfinite

open RankTwo Cardinal Set

noncomputable section

abbrev AtlasIndex (κ : Cardinal.{0}) := (Order.succ κ).ord.ToType

variable {I : Type} [LinearOrder I]

/-- Label each club position by the unit vector at the corresponding index point. -/
def ladders (κ : Cardinal.{0}) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o I) : CoherentLadders (AtlasIndex κ) (Letter I) :=
  S.labelled (Ordinal.ToType.mk.toOrderEmbedding.trans
    (slots.trans (OrderEmbedding.ofStrictMono unitLetter unitLetter_strictMono)))

def transports (i : I) (κ : Cardinal.{0}) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o I) : (ladders κ S slots).markedRows.Transports :=
  (ladders κ S slots).transports Word.shiftLetter ⟨0,le_rfl⟩
    (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter

/-- The actual frame maps with the prescribed coordinate algebra. -/
abbrev LargeFrames (i : I) (κ : Cardinal.{0}) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o I) :=
  (ladders κ S slots).markedRows.Frames (transports i κ S slots) (Concrete.family i)

def largeAnchor (i : I) (κ : Cardinal.{0}) (S : SquareLadders (AtlasIndex κ) κ.ord)
    (slots : κ.ord.ToType ↪o I) (a : AtlasIndex κ) : LargeFrames i κ S slots :=
  (ladders κ S slots).markedRows.frameAnchor (transports i κ S slots) (Concrete.family i) a

/-- The anchors have strictly increasing endpoints, independently of the
linear order chosen later on each common-endpoint fiber. -/
theorem largeAnchor_strictMono_endpoint (i : I) (κ : Cardinal.{0})
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I) :
    StrictMono (fun a => (largeAnchor i κ S slots a).val ⊤) := by
  intro a b h
  simp only [largeAnchor,MarkedRows.frameAnchor_top]
  exact (ladders κ S slots).markedRows.anchor_strictMono h

def largeAction (i : I) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I) :
    Scott.FrameAction (Concrete.Code i) (LargeFrames i κ S slots) := by
  letI : NoMaxOrder (AtlasIndex κ) := Cardinal.noMaxOrder (hκ.trans (Order.le_succ κ))
  exact (ladders κ S slots).largeFrameAction Word.shiftLetter ⟨0,le_rfl⟩
    (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter

theorem mk_vector_le (i : I) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) :
    #(VectorGroup I) ≤ κ := by
  letI : Nonempty I := ⟨i⟩
  change #(I →₀ ℚ) ≤ κ
  rw [mk_finsupp_of_infinite',Cardinal.mkRat]
  exact max_le hI hκ

theorem mk_words_le (i : I) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) :
    #(List (Letter I)) ≤ κ :=
  (mk_list_le_max _).trans (max_le hκ ((mk_subtype_le _).trans (mk_vector_le i hκ hI)))

theorem mk_largeFrames (i : I) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o I)
    (hI : #I ≤ κ) : #(LargeFrames i κ S slots) = Order.succ κ := by
  have hJ : #(AtlasIndex κ) = Order.succ κ := by rw [mk_toType,card_ord]
  have hc : #(Concrete.Code i) ≤ κ := mk_schematic_code _ _ _ _ _ _ hκ (mk_words_le i hκ hI)
  exact ((ladders κ S slots).markedRows.cardinal_frames (transports i κ S slots)
    (Concrete.family i) (hJ ▸ hκ.trans (Order.le_succ κ)) (hJ ▸ hc.trans (Order.le_succ κ))).trans hJ

end
end KnightModel.Transfinite
