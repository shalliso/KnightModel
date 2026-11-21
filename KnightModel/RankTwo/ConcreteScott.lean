import KnightModel.RankTwo.ConcreteCoordinates
import KnightModel.RankTwo.ConcreteRunMatch
import KnightModel.RankTwo.ScottIntervals
import KnightModel.RankTwo.ScottCountable

/-! # The square model satisfies the Scott sentence of the countable frame model -/

namespace KnightModel.RankTwo.Concrete

open Scott Cardinal

instance {B K : ℕ → Type} [∀ n, Countable (B n)] [∀ n, Countable (K n)] (n : ℕ) :
    Countable (FrameRelation B K n) := by
  let Codes := (Σ k, B k) ⊕ (Unit ⊕ (Unit ⊕ (Σ k, K k)))
  let decode : Codes → Σ k, FrameRelation B K k
    | .inl ⟨k, b⟩ => ⟨k, .base b⟩
    | .inr (.inl _) => ⟨1, .frame⟩
    | .inr (.inr (.inl _)) => ⟨2, .below⟩
    | .inr (.inr (.inr ⟨k, s⟩)) => ⟨k + 2, .transition s⟩
  have onto : Function.Surjective decode := by
    rintro ⟨_, r⟩
    cases r with
    | base b => exact ⟨.inl ⟨_, b⟩, rfl⟩
    | frame => exact ⟨.inr (.inl ()), rfl⟩
    | below => exact ⟨.inr (.inr (.inl ())), rfl⟩
    | transition k => exact ⟨.inr (.inr (.inr ⟨_, k⟩)), rfl⟩
  haveI : Countable (Σ k, FrameRelation B K k) := onto.countable
  exact (show Function.Injective (Sigma.mk n : FrameRelation B K n → Σ k, FrameRelation B K k)
    from sigma_mk_injective).countable

variable {Ω I J : Type} [Blueprint Ω] [KnightModel I Ω] [KnightModel J Ω]
    [Nonempty I] [Nonempty J]

/-- The ordinary countable-language Scott presentation of the small model. -/
noncomputable def presentation [Countable I] (i : I) :
    Presentation (FrameRelation (BaseRelation Ω) Name) (SmallCarrier I i) := by
  letI := countable_small (Ω := Ω) i
  exact Presentation.ofCountable _ _

theorem interprets_frames (i : I) (j : J) (S : SquareLadders OuterIndex (aleph 1).ord)
    (unc : ¬ Countable J) :
    (frameMatches (intervalMatches (Ω := Ω) i j) S unc).Interprets
      (smallInterpretation (Ω := Ω) i) (largeInterpretation S unc j) where
  param_eq := BaseMatch.eq_iff
  code_eq h k := graphEq.symm.trans ((GraphMatch.same h k).trans graphEq)
  base {p n} r {s t} h := BaseMatch.base_iff p.property r h
  run {p n} k {s t} h := run_matches (intervalMatches (Ω := Ω) i j) p.property k h

/-- At every matched distinguished point the actual three-sorted large model
realizes the small model's countable infinitary Scott sentence. -/
theorem large_satisfies [Countable I] (i : I) (j : J) (p : ModelIsoCondition I J Ω)
    (mark : (i, j) ∈ p.graph) (S : SquareLadders OuterIndex (aleph 1).ord)
    (unc : ¬Countable J) :
    BackAndForth.Satisfies (largeModel (Ω := Ω) S unc j)
      ((presentation (Ω := Ω) i).sentence (smallModel i)) := by
  let z := Word.cons (unitLetter i) Word.root
  let f := throughCode Word.shiftLetter (⟨0, le_rfl⟩ : Letter I) (unitLetter i)
    (zero_lt_unit i) Word.shiftOpenLetter z
  have hf : f.val ⊤ = z := throughCode_top _ _ _ _ _ _
  let u : SmallFrames i := ⟨f, hf ▸ Word.cons_lt_root _ _⟩
  let b : OuterIndex := Ordinal.ToType.mk ⟨0, Cardinal.ord_pos.mpr (Cardinal.aleph_pos 2)⟩
  let C := knightLadders (Ω := Ω) S unc
  let v : LargeFrames (Ω := Ω) S unc j :=
    C.markedRows.frameAnchor (knightTransports (Ω := Ω) S unc j) (family j) b
  exact (interprets_frames i j S unc).satisfies (presentation i) ⟨p, mark⟩ u v

end KnightModel.RankTwo.Concrete
