import KnightModel.RankTwo.ScottRestrictionLabels
import KnightModel.RankTwo.RestrictionSkeleton

/-! # From small profiles on comparison chains to all singleton-orbit profiles

An uncountable family of distinct profiles gives an ω₁-indexed family of
representatives. A single base puts them and all parameters inside its
rank-one part. One relative orbit still contains uncountably many of the
representatives, and its rank-zero lower cones give a comparison subchain.
-/

namespace KnightModel.RankTwo.Scott

open Cardinal Restriction Set

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

private abbrev singlePoint {X : Type} (x : X) : Tuple X 1 := push x Fin.elim0

/-- A parameter is in its own definable closure, in every Scott model. -/
theorem mem_lowFiber_self {k} (z : N) (t : Tuple N k) :
    z ∈ lowFiber (C.system D E sat) 0 (push z t) := by
  let F := C.system D E sat
  obtain ⟨s, hs⟩ := SentenceLabels.exists_label C D E sat (push z t)
  have lifts := (SentenceLabels.lifts_iff C D E sat _ _).mpr hs
  refine ⟨s 0, s, fun g h => h (s 0) (List.mem_ofFn.mpr ⟨0,rfl⟩), ?_⟩
  let q : Fin (k+2) → Fin (k+1) := Fin.cases 0 id
  have r := lifts.select F q
  change F.Lifts (push (s 0) s) (push z (push z t))
  convert r using 1 <;> funext i <;> exact Fin.cases rfl (fun _ => rfl) i

private theorem preimage_card_le {X Y : Type} (f : X → Y) (hf : Function.Injective f)
    (s : Set Y) : #(f ⁻¹' s) ≤ #s := by
  let e (x : f ⁻¹' s) : s := ⟨f x.val,x.property⟩
  exact mk_le_of_injective (f := e) fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

/-- The global step used for one-point orbital diagrams. The profile can take
values in any set; the local hypothesis is needed only on rank-zero chains. -/
theorem countable_range_of_scott_chains {Y A : Type} [Countable A] (x : M)
    (rank : ModelRankLE D 2 [] x)
    (big : ℵ₁ < #(orbitFiber (C.system D E sat) Fin.elim0 x Fin.elim0))
    (params : A → orbitFiber (C.system D E sat) Fin.elim0 x Fin.elim0) (profile : N → Y)
    (chains : ∀ (d : N) (f : OmegaOne → N),
      (∀ a, (params a).val ∈ lowFiber (C.system D E sat) 1 (singlePoint d)) →
      (∀ i j, i ≤ j → f i ∈ lowFiber (C.system D E sat) 0 (push (f j) (singlePoint d))) →
      (range (profile ∘ f)).Countable) :
    (range (fun b : orbitFiber (C.system D E sat) Fin.elim0 x Fin.elim0 => profile b.val)).Countable := by
  classical
  let F := C.system D E sat
  let O := orbitFiber F Fin.elim0 x Fin.elim0
  let p (b : O) := profile b.val
  by_contra hsmall
  have uncount : ℵ₁ ≤ #(range p) := aleph_one_le_iff.mpr <| lt_of_not_ge
    (fun hh => hsmall (le_aleph0_iff_set_countable.mp hh))
  have hOne : #OmegaOne = ℵ₁ := by simp only [mk_toType, card_ord]
  obtain ⟨index⟩ := (le_def OmegaOne (range p)).mp (hOne ▸ uncount)
  let reps (i : OmegaOne) : O := (index i).property.choose
  have hrep (i : OmegaOne) : p (reps i) = (index i).val := (index i).property.choose_spec
  have distinct : Function.Injective (p ∘ reps) := by
    intro i j e
    exact index.injective (Subtype.ext ((hrep i).symm.trans (e.trans (hrep j))))
  have repInj : Function.Injective (fun i => (reps i).val) := fun _ _ e => distinct (congrArg profile e)
  have ho : O.Nonempty := ⟨_, (reps omegaOneStages.start).property⟩
  have hr : ModelRankLE D (1+1) (List.ofFn (Fin.elim0 : Tuple M 0)) x := by simpa using rank
  rcases orbitFiber_dichotomy F C Fin.elim0 x Fin.elim0 hr ho with ⟨d, covers⟩ | compare
  · exact big.not_ge ((mk_le_mk_of_subset covers).trans (by simpa using lowFiber_cardinal F C 1 (singlePoint d)))
  let lower (b : O) : Set O := Subtype.val ⁻¹' lowFiber F 1 (singlePoint b.val)
  have small (b : O) : #(lower b) ≤ ℵ₁ := (preimage_card_le Subtype.val Subtype.val_injective _).trans
    (by simpa using lowFiber_cardinal F C 1 (singlePoint b.val))
  have cmp (a b : O) : a ∈ lower b ∨ b ∈ lower a := (compare _ a.property _ b.property).symm
  have hI : #(A ⊕ OmegaOne) ≤ ℵ₁ := by
    rw [mk_sum, lift_id, lift_id, hOne, add_eq_right (aleph0_le_aleph 1)
      ((mk_le_aleph0 (α := A)).trans (aleph0_le_aleph 1))]
  obtain ⟨d, hd⟩ := common_comparison_witness (aleph0_le_aleph 1) big hI lower small cmp
    (Sum.elim params reps)
  have parameterLow (a : A) : (params a).val ∈ lowFiber F 1 (singlePoint d.val) := (hd (.inl a)).1
  have labels (i : OmegaOne) : ∃ q : M × Tuple M 1, ModelRankLE D 1 (List.ofFn q.2) q.1 ∧
      (reps i).val ∈ orbitFiber F q.2 q.1 (singlePoint d.val) := by
    obtain ⟨w,s,hw,he⟩ := (show (reps i).val ∈ lowFiber F 1 (singlePoint d.val) from (hd (.inr i)).1)
    exact ⟨(w,s), hw, he⟩
  let label (i : OmegaOne) := (labels i).choose
  haveI : Countable M := Function.Surjective.countable (f := C.enum) C.onto
  obtain ⟨q, hq⟩ := infinite_pigeonhole label
    (by rw [hOne]; exact aleph0_le_aleph 1)
    (by rw [hOne,isRegular_aleph_one.cof_ord]; exact mk_le_aleph0.trans_lt aleph0_lt_aleph_one)
  let I := label ⁻¹' {q}
  have largeI : ℵ₀ < #I := by rw [show #I = #OmegaOne from hq, hOne]; exact aleph0_lt_aleph_one
  have hlabel (i : I) : ModelRankLE D 1 (List.ofFn q.2) q.1 ∧
      (reps i.val).val ∈ orbitFiber F q.2 q.1 (singlePoint d.val) := by
    have eq : label i.val = q := i.property
    exact eq ▸ (labels i.val).choose_spec
  have nonemptyI : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := not_nonempty_iff.mp h
    simp at largeI
  let i₀ := Classical.choice nonemptyI
  let g (i : I) := (reps i.val).val
  have injg : Function.Injective g := fun _ _ e => Subtype.ext (repInj e)
  let J := orbitFiber F q.2 q.1 (singlePoint d.val)
  have hJ : J.Nonempty := ⟨_, (hlabel i₀).2⟩
  rcases orbitFiber_dichotomy F C q.2 q.1 (singlePoint d.val) (hlabel i₀).1 hJ with ⟨w, cap⟩ | pair
  · have bound : #(g ⁻¹' lowFiber F 0 (push w (singlePoint d.val))) ≤ ℵ₀ :=
      (preimage_card_le g injg _).trans (by simpa using lowFiber_cardinal F C 0 (push w (singlePoint d.val)))
    have eq : (g ⁻¹' lowFiber F 0 (push w (singlePoint d.val))) = Set.univ :=
      eq_univ_of_forall fun i => cap (hlabel i).2
    exact largeI.not_ge (by simpa only [eq,mk_univ] using bound)
  let cone (i : I) := g ⁻¹' lowFiber F 0 (push (g i) (singlePoint d.val))
  have count (i : I) : (cone i).Countable := (le_aleph0_iff_set_countable.mp
    (by simpa using lowFiber_cardinal F C 0 (push (g i) (singlePoint d.val)))).preimage injg
  have cmpI (i j : I) : i ∈ cone j ∨ j ∈ cone i := (pair _ (hlabel i).2 _ (hlabel j).2).symm
  obtain ⟨seq, hseq⟩ := omegaOne_comparison_subchain largeI cone count cmpI
  have smallRange := chains d.val (g ∘ seq) parameterLow (by
    intro i j hij
    rcases hij.eq_or_lt with rfl | h
    · exact mem_lowFiber_self C sat _ _
    · exact (hseq i j h).1)
  have inj : Function.Injective (profile ∘ (g ∘ seq)) := fun _ _ eq =>
    seq.injective (Subtype.ext (distinct eq))
  have bound := le_aleph0_iff_set_countable.mpr smallRange
  rw [mk_range_eq _ inj,hOne] at bound
  exact aleph0_lt_aleph_one.not_ge bound

end KnightModel.RankTwo.Scott
