import KnightModel.Transfinite.OrderTransfer
import KnightModel.Transfinite.FrameOrderInvariant
import Mathlib.Data.Sum.Order

/-! # The pointed, linearly ordered countable successor

The whole sort is the ordered sum of the old points, their finitely supported
vectors and the proper charts. Each chart fiber carries the intrinsic comparison
of its coordinate maps. The old distinguished point remains named.
-/

namespace KnightModel.Transfinite

open RankTwo Scott
noncomputable section

/-- The actual inherited unary mark of a frame expansion. -/
private theorem frame_mark {R : Nat → Type} {I C F : Type} [LinearOrder I]
    {D : Model R I} {A : FrameAction C F}
    (T : FrameInterpretation (BaseRelation R) Concrete.Name (BasePoints I) A)
    (base : T.base (k := 1) = baseModel D (k := 1)) (r : R 1) (i : I)
    (hr : ∀ t, D r t ↔ t 0 = i)
    (s : Tuple (BasePoints I ⊕ F) 1) :
    T.model (.base (.old r)) s ↔ s 0 = .inl (.inl i) := by
  change (∃ t, (∀ j, s j = .inl (t j)) ∧ T.base (.old r) t) ↔ _
  rw [base]
  constructor
  · rintro ⟨t,ht,u,hu,h⟩
    rw [ht 0,hu 0,(hr u).mp h]
  · intro h
    refine ⟨fun _ => .inl i, fun j => ?_, fun _ => i, fun _ => rfl, (hr _).mpr rfl⟩
    exact (Subsingleton.elim j 0) ▸ h

theorem small_mark (P : Seed) (s : Tuple (SmallCarrier P.mark) 1) :
    smallModel P.D P.mark (.base (.old P.markSym)) s ↔ s 0 = .inl (.inl P.mark) :=
  frame_mark _ rfl _ _ P.mark_iff _

theorem large_mark (P : Seed) {κ} (Q : P.Realizes κ) (hκ : Cardinal.aleph0 ≤ κ)
    (S : SquareLadders (AtlasIndex κ) κ.ord) (s : Tuple (LargeCarrier Q.mark κ S Q.seq) 1) :
    largeModel Q.E Q.mark κ hκ S Q.seq (.base (.old P.markSym)) s ↔ s 0 = .inl (.inl Q.mark) :=
  frame_mark _ rfl _ _ Q.mark_iff _

abbrev successorOrder (P : Seed) : LinearOrder (SmallCarrier P.mark) :=
  letI := FrameOrder.order P.mark
  inferInstanceAs (LinearOrder ((P.M ⊕ₗ VectorGroup P.M) ⊕ₗ Concrete.SmallFrames P.mark))

/-- Every automorphism of the full raw structure preserves the order on its whole carrier. -/
theorem successorOrder_invariant (P : Seed) (g : ↥(automorphismGroup (smallModel P.D P.mark)))
    (x y : SmallCarrier P.mark) :
    letI := successorOrder P
    x ≤ y ↔ g • x ≤ g • y := by
  letI := FrameOrder.order P.mark
  let perm := (SuccessorAut.frameSort P).map g
  let f : Concrete.SmallFrames P.mark ≃o Concrete.SmallFrames P.mark :=
    { toEquiv := (SuccessorAut.frameSort P).perm g
      map_rel_iff' := fun {a b} => by
        change (FrameOrder.order P.mark).le (perm a) (perm b) ↔ (FrameOrder.order P.mark).le a b
        exact (not_lt (a := perm b) (b := perm a)).symm.trans
          ((not_congr (FrameOrder.aut_lt_iff P g b a)).symm.trans not_lt) }
  let e := ((SuccessorAut.indexOrderIso P g).sumLexCongr
    (SuccessorAut.vectorOrderIso P g)).sumLexCongr f
  have act (u : SmallCarrier P.mark) : e u = g • u := by
    rcases u with (u|v)|w
    · exact (SuccessorAut.indexSort P).incl_map g u
    · exact (SuccessorAut.vectorSort P).incl_map g v
    · exact (SuccessorAut.frameSort P).incl_map g w
  exact (e.le_iff_le (x := x) (y := y)).symm.trans (by rw [act,act]; rfl)

/-- The countable successor is fixed before choosing any large realization or square sequence. -/
def successorSeed (P : Seed) : Seed :=
  letI := successorOrder P
  letI := countable_smallCarrier P.mark
  orderedSeed (smallModel P.D P.mark) (.inl (.inl P.mark)) (.base (.old P.markSym)) (small_mark P)

end
end KnightModel.Transfinite
