import KnightModel.RankTwo.ScottTupleThinning
import KnightModel.RankTwo.ScottRestrictionTupleProfiles

/-! # Countably many orbital diagrams of tuples of any fixed finite arity -/

namespace KnightModel.RankTwo.Scott

open Set Cardinal Restriction

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

local notation "F" => C.system D E sat

/-- In a Scott model a relative rank bound persists when every old base
parameter occurs among the coordinates of a new finite base. -/
theorem lowFiber_enlarge {m n r : ℕ} {t : Tuple N m} {u : Tuple N n} {z : N}
    (incl : ∀ i, ∃ j, u j = t i) (hz : z ∈ lowFiber F r t) : z ∈ lowFiber F r u := by
  classical
  obtain ⟨w, hw⟩ := SentenceLabels.exists_label C D E sat (push z u)
  have big := (SentenceLabels.lifts_iff C D E sat _ _).mpr hw
  let s := Fin.tail w
  let f := fun i => (incl i).choose
  let sel : Fin (m+1) → Fin (n+1) := Fin.cases 0 fun i => (f i).succ
  have ew : w = push (w 0) s := (Fin.cons_self_tail w).symm
  have e₁ : w ∘ sel = push (w 0) (s ∘ f) := funext (Fin.cases rfl (fun _ => rfl))
  have e₂ : push z u ∘ sel = push z t := funext (Fin.cases rfl (fun i => (incl i).choose_spec))
  have small := big.select F sel
  rw [e₁, e₂] at small
  have rank := ((F).lowFiber_iff_liftRank C small).mp hz
  exact ((F).lowFiber_iff_liftRank C (ew ▸ big)).mpr (rank.mono_params (by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact List.mem_ofFn.mpr ⟨f j, rfl⟩))

private theorem coordinate_enlarge {B : List N} {m : ℕ} (s : Tuple N m) (j : Fin m) {z : N}
    (hz : z ∈ lowFiber F 0 (push (s j) B.get)) :
    z ∈ lowFiber F 0 ((List.ofFn s) ++ B).get := by
  apply lowFiber_enlarge C sat _ hz
  intro l
  apply List.mem_iff_get.mp
  exact Fin.cases (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    (fun i => List.mem_append_right _ (List.get_mem _ i)) l

/-- The entire finite-tuple orbital diagram over a parameter enumeration. -/
noncomputable def finiteDiagram {A : Type} {m : ℕ} (z : A → N) (t : Tuple N m)
    (u : Sigma (Tuple A)) : ℕ :=
  SentenceLabels.number C D E sat (Fin.addCases t (z ∘ u.2))

/-- If the parameters and every endpoint entry have rank at most one over a
single common base, every countable parameter set supports only countably many
finite-tuple diagrams in this family. -/
theorem countable_finite_diagrams_low {A X : Type} [Countable A] {m : ℕ}
    (B : List N) (z : A → N) (v : X → Tuple N m)
    (params : ∀ a, z a ∈ lowFiber F 1 B.get) (low : ∀ i j, v i j ∈ lowFiber F 1 B.get) :
    (range (fun x => finiteDiagram C sat z (v x))).Countable := by
  classical
  let profile := fun x => finiteDiagram C sat z (v x)
  by_contra uncount
  have large : ℵ₁ ≤ #(range profile) := aleph_one_le_iff.mpr <| lt_of_not_ge
    (fun le => uncount (le_aleph0_iff_set_countable.mp le))
  have size : #OmegaOne = ℵ₁ := by simp only [mk_toType, card_ord]
  obtain ⟨e⟩ := (le_def OmegaOne (range profile)).mp (size ▸ large)
  let reps (i : OmegaOne) := (e i).property.choose
  have injective : Function.Injective (profile ∘ reps) := fun i j h => e.injective
    (Subtype.ext ((e i).property.choose_spec.symm.trans (h.trans (e j).property.choose_spec)))
  have many : ¬ (univ : Set OmegaOne).Countable := by
    intro h
    have c := le_aleph0_iff_set_countable.mpr h
    rw [mk_univ, size] at c
    exact aleph0_lt_aleph_one.not_ge c
  obtain ⟨f, _, chain⟩ := low_tuple_comparison_chain C sat B.get (v ∘ reps) (fun i => low _) univ many
  let y i := v (reps (f i))
  have small := SentenceLabels.chain_tuple_profiles C D E sat B y
    (fun i j ij l => coordinate_enlarge C sat (y j) l (chain i j ij l)) z params
  let g := (profile ∘ reps) ∘ f
  have hsmall : (range g).Countable := small
  have card := le_aleph0_iff_set_countable.mpr hsmall
  rw [mk_range_eq g (injective.comp f.injective), size] at card
  exact aleph0_lt_aleph_one.not_ge card

/-- With global singleton rank at most one, every finite arity has countably
many realized orbital diagrams over any countable parameter family. -/
theorem countable_finite_diagrams_rank_one (rank : ∀ x : M, ModelRankLE D 1 [] x)
    {A : Type} [Countable A] (z : A → N) (m : ℕ) :
    (range (finiteDiagram C sat (m := m) z)).Countable := by
  have all (y : N) : y ∈ lowFiber F 1 ([] : List N).get := by
    obtain ⟨w, hw⟩ := SentenceLabels.exists_label C D E sat (push y ([] : List N).get)
    have lift := (SentenceLabels.lifts_iff C D E sat _ _).mpr hw
    have he : w = push (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    exact ((F).lowFiber_iff_liftRank C (he ▸ lift)).mpr (by simpa using rank (w 0))
  exact countable_finite_diagrams_low C sat [] z id (fun a => all _) (fun w j => all _)

private theorem countable_range_of_subfamilies {X Y : Type} (f : X → Y)
    (small : ∀ r : OmegaOne → X, (range (f ∘ r)).Countable) : (range f).Countable := by
  by_contra uncount
  have large : ℵ₁ ≤ #(range f) := aleph_one_le_iff.mpr <| lt_of_not_ge
    (fun le => uncount (le_aleph0_iff_set_countable.mp le))
  have size : #OmegaOne = ℵ₁ := by simp only [mk_toType, card_ord]
  obtain ⟨e⟩ := (le_def OmegaOne (range f)).mp (size ▸ large)
  let r (i : OmegaOne) := (e i).property.choose
  have inj : Function.Injective (f ∘ r) := fun i j h => e.injective
    (Subtype.ext ((e i).property.choose_spec.symm.trans (h.trans (e j).property.choose_spec)))
  have card := le_aleph0_iff_set_countable.mpr (small r)
  rw [mk_range_eq _ inj, size] at card
  exact aleph0_lt_aleph_one.not_ge card

/-- In a rank-two singleton orbit of size greater than ℵ₁, a countable
parameter family supports at most countably many diagrams of every fixed
finite arity of points from that orbit. -/
theorem countable_finite_diagrams_rank_two {A : Type} [Countable A] (x : M)
    (rank : ModelRankLE D 2 [] x) (big : ℵ₁ < #(orbitFiber F Fin.elim0 x Fin.elim0))
    (params : A → orbitFiber F Fin.elim0 x Fin.elim0) (m : ℕ) :
    (range (fun t : Fin m → orbitFiber F Fin.elim0 x Fin.elim0 =>
      finiteDiagram C sat (fun a => (params a).val) (fun j => (t j).val))).Countable := by
  classical
  let O := orbitFiber F Fin.elim0 x Fin.elim0
  have nonempty : Nonempty O := mk_ne_zero_iff.mp (ne_of_gt (zero_le.trans_lt big))
  obtain ⟨b⟩ := nonempty
  have rank' : ModelRankLE D (1+1) (List.ofFn (Fin.elim0 : Tuple M 0)) x := by simpa using rank
  rcases orbitFiber_dichotomy F C Fin.elim0 x Fin.elim0 rank' ⟨b.val,b.property⟩ with ⟨d,cap⟩ | pair
  · exact (big.not_ge ((mk_le_mk_of_subset cap).trans
      (by simpa using lowFiber_cardinal F C 1 (push d Fin.elim0)))).elim
  let lower (z : O) : Set O := Subtype.val ⁻¹' lowFiber F 1 (push z.val Fin.elim0)
  have bound (z : O) : #(lower z) ≤ ℵ₁ := by
    let e (s : lower z) : lowFiber F 1 (push z.val Fin.elim0) := ⟨s.val.val, s.property⟩
    have inj : Function.Injective e := fun a b h => Subtype.ext (Subtype.ext
      (congrArg (fun q : lowFiber F 1 (push z.val Fin.elim0) => q.val) h))
    exact (mk_le_of_injective inj).trans (by simpa using lowFiber_cardinal F C 1 (push z.val Fin.elim0))
  have cmp (a b : O) : a ∈ lower b ∨ b ∈ lower a := (pair _ a.property _ b.property).symm
  apply countable_range_of_subfamilies
  intro r
  have size : #OmegaOne = ℵ₁ := by simp only [mk_toType, card_ord]
  have prod : #(OmegaOne × Fin m) ≤ ℵ₁ := by
    rw [mk_prod, lift_id, lift_id, size]
    exact (mul_le_mul' le_rfl ((mk_le_aleph0 (α := Fin m)).trans (aleph0_le_aleph 1))).trans_eq
      (mul_eq_self (aleph0_le_aleph 1))
  have width : #(A ⊕ (OmegaOne × Fin m)) ≤ ℵ₁ := by
    rw [mk_sum, lift_id, lift_id]
    exact (add_le_add ((mk_le_aleph0 (α := A)).trans (aleph0_le_aleph 1)) prod).trans_eq
      (add_eq_self (aleph0_le_aleph 1))
  let both : A ⊕ (OmegaOne × Fin m) → O := Sum.elim params (fun p => r p.1 p.2)
  obtain ⟨d,hd⟩ := common_comparison_witness (aleph0_le_aleph 1) big width lower bound cmp both
  have same : [d.val].get = push d.val (Fin.elim0 : Fin 0 → N) :=
    funext (Fin.cases rfl (fun i => i.elim0))
  exact countable_finite_diagrams_low C sat [d.val] (fun a => (params a).val)
    (fun i j => (r i j).val) (fun a => same.symm ▸ (hd (.inl a)).1)
    (fun i j => same.symm ▸ (hd (.inr (i,j))).1)

end KnightModel.RankTwo.Scott
