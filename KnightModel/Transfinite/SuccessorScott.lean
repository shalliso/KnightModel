import KnightModel.Transfinite.SuccessorOrder
import KnightModel.Transfinite.SuccessorRank
import KnightModel.Transfinite.TransferFrames

/-! # Successor realization and rank bound

Given a realization of size κ with an increasing κ-sequence and a square
sequence at κ, the fixed countable successor seed has a realization of size
κ⁺ with an increasing κ⁺-sequence. The rank estimate on the countable
structure is independent of the square sequence.
-/

namespace KnightModel.Transfinite

open RankTwo Scott Cardinal
noncomputable section

variable (P : Seed) {κ : Cardinal.{0}} (Q : P.Realizes κ) (hκ : ℵ₀ ≤ κ)
variable (S : SquareLadders (AtlasIndex κ) κ.ord)

private def oldSystem : OrderedBF P.D Q.E :=
  OrderedBF.ofNamed (P.pres.system P.D Q.E Q.sat) P.leSym P.le_iff Q.le_iff

/-- The large raw frame structure and the actual countable successor share a
back-and-forth which extends the given one on the old structures. -/
def successorTransfer : letI := successorOrder P
    OrderTransfer (smallModel P.D P.mark) (largeModel Q.E Q.mark κ hκ S Q.seq) := by
  letI := successorOrder P
  exact {
    F := frameSystem (oldSystem P Q) P.mark Q.mark κ hκ S Q.seq
    empty := by
      have empty : (oldSystem P Q).matchTuples (n := 0) Fin.elim0 Fin.elim0 :=
        ((P.pres.sentence_iff P.D Q.E).mp Q.sat).1
      have m := frameSystem_old (oldSystem P Q) P.mark Q.mark κ hκ S Q.seq
        P.markSym P.mark_iff Q.mark_iff empty
      let s (l : Fin 0) : SmallCarrier P.mark := .inl (.inl (Fin.elim0 l))
      let t (l : Fin 0) : LargeCarrier Q.mark κ S Q.seq := .inl (.inl (Fin.elim0 l))
      exact (Subsingleton.elim s Fin.elim0) ▸ (Subsingleton.elim t Fin.elim0) ▸ m
    pres := smallPresentation P.mark
    invariant := successorOrder_invariant P
  }

private theorem model_below {B K : Nat → Type} {U C F : Type} {A : FrameAction C F}
    (T : FrameInterpretation B K U A) (s : Tuple (U ⊕ F) 2) {a b : F}
    (h0 : s 0 = .inr a) (h1 : s 1 = .inr b) : T.model .below s ↔ A.Below a b := by
  constructor
  · rintro ⟨v,c,hx,hy⟩
    obtain rfl : b = v := Sum.inr.inj (h1.symm.trans hy)
    exact ⟨c,Sum.inr.inj (hx.symm.trans h0)⟩
  · rintro ⟨c,rfl⟩
    exact ⟨b,c,h0,h1⟩

private theorem large_below (a b : LargeFrames Q.mark κ S Q.seq) :
    (largeAction Q.mark κ hκ S Q.seq).Below a b ↔ a.val ⊤ ≤ b.val ⊤ :=
  ((ladders κ S Q.seq).markedRows.below_frame_iff (transports Q.mark κ S Q.seq)
    (Concrete.family Q.mark) (fun h => (ladders κ S Q.seq).change_allowed Word.shiftLetter
      ⟨0,le_rfl⟩ (unitLetter Q.mark) (zero_lt_unit Q.mark) Word.shiftOpenLetter h)).symm

/-- Increasing endpoints of large charts remain strictly increasing in the
transferred linear order, including when its same-endpoint fibers are nontrivial. -/
theorem successor_frame_lt (a b : LargeFrames Q.mark κ S Q.seq) (hab : a.val ⊤ < b.val ⊤) :
    letI := successorOrder P
    letI := (successorTransfer P Q hκ S).order
    (Sum.inr a : LargeCarrier Q.mark κ S Q.seq) < .inr b := by
  letI := successorOrder P
  let T := successorTransfer P Q hκ S
  letI := T.order
  let t : Tuple (LargeCarrier Q.mark κ S Q.seq) 2 := ![.inr a,.inr b]
  obtain ⟨s,h⟩ := T.exists_lift t
  have frame (j : Fin 2) (f : LargeFrames Q.mark κ S Q.seq) (ht : t j = .inr f) :
      ∃ c : Concrete.SmallFrames P.mark, s j = .inr c :=
    (T.F.closure.atoms h (.rel .frame (fun _ => j))).mpr ⟨f,ht⟩
  obtain ⟨u,hu⟩ := frame 0 a rfl
  obtain ⟨v,hv⟩ := frame 1 b rfl
  have endpoint {i j : Fin 2} {c d : Concrete.SmallFrames P.mark}
      {f g : LargeFrames Q.mark κ S Q.seq}
      (sc : s i = .inr c) (sd : s j = .inr d) (tf : t i = .inr f) (tg : t j = .inr g) :
      c.val.val ⊤ ≤ d.val.val ⊤ ↔ f.val ⊤ ≤ g.val ⊤ := by
    let ij : Fin 2 → Fin 2 := ![i,j]
    exact (FrameOrder.small_below_iff P.mark c d).symm.trans
      ((model_below (smallInterpretation P.D P.mark) (s ∘ ij) sc sd).symm.trans
        ((T.F.closure.atoms h (.rel .below ij)).trans
          ((model_below (largeInterpretation Q.E Q.mark κ hκ S Q.seq) (t ∘ ij) tf tg).trans
            (large_below P Q hκ S f g))))
  have hlt : u.val.val ⊤ < v.val.val ⊤ :=
    lt_of_not_ge (fun back => hab.not_ge ((endpoint hv hu (show t 1 = .inr b from rfl)
      (show t 0 = .inr a from rfl)).mp back))
  apply (T.lt_iff h 0 1).mp
  rw [hu,hv]
  letI := FrameOrder.order P.mark
  exact (Sum.Lex.inr_lt_inr_iff (α := P.M ⊕ₗ VectorGroup P.M)
    (β := Concrete.SmallFrames P.mark)).mpr (FrameOrder.lt_of_endpoint_lt P.mark hlt)

/-- Actual successor realization, including a linearly increasing sequence of
full successor length for use as slots at the next stage. -/
def successorRealizes : (successorSeed P).Realizes (Order.succ κ) := by
  letI := successorOrder P
  let T := successorTransfer P Q hκ S
  letI := T.order
  exact {
    N := LargeCarrier Q.mark κ S Q.seq
    E := orderedModel (largeModel Q.E Q.mark κ hκ S Q.seq)
    ord := T.order
    mark := .inl (.inl Q.mark)
    le_iff := fun _ => Iff.rfl
    mark_iff := large_mark P Q hκ S
    sat := T.satisfies (successorSeed P).pres
    seq := OrderEmbedding.ofStrictMono (fun a => .inr (largeAnchor Q.mark κ S Q.seq a))
      (fun _ _ hab => successor_frame_lt P Q hκ S _ _
        (largeAnchor_strictMono_endpoint Q.mark κ S Q.seq hab))
    size := mk_largeCarrier Q.mark κ hκ S Q.seq Q.size.le }

/-- Naming the order preserves the successor comparison bound on every finite tuple. -/
theorem successorSeed_tuple_comparisonLE {α : Ordinal.{0}} (hα : α ≠ 0)
    (old : ∀ n (p : Fin n → P.M), ComparisonLT α (⊤ : Subgroup ↥(automorphismGroup P.D)) p)
    (n : ℕ) (x : Fin n → (successorSeed P).M) :
    ComparisonLE α (⊤ : Subgroup ↥(automorphismGroup (successorSeed P).D)) x := by
  letI := successorOrder P
  exact ComparisonLE.of_hom (orderedAutHom (smallModel P.D P.mark)) (fun _ _ => Subgroup.mem_top _)
    (fun _ _ => Iff.rfl) (successor_tuple_comparisonLE P hα old n x)

end
end KnightModel.Transfinite
