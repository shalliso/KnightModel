import KnightModel.Transfinite.ComparisonOrdinalTransport
import KnightModel.RankTwo.Spectrum

/-! # Sharp cardinal upper bounds for ordinal disjointifying rank

A lower ordinal in the comparison clause can depend on the conjugate. Over a
fixed target tuple the countably many earlier source labels have total size
at most the supremum of their cardinal bounds. The pair-cover estimate then
takes one cardinal successor.
-/

namespace KnightModel.Transfinite

open RankTwo RankTwo.Scott Cardinal Set
universe w
noncomputable section

/-- Index of the cardinal bound for singleton rank at most α. -/
def ceilingIndex (α : Ordinal.{0}) : Ordinal.{0} :=
  if α < Ordinal.omega0 then α else Order.succ α

theorem ceilingIndex_le_of_lt {β α : Ordinal.{0}} (h : β < α) : ceilingIndex β ≤ α := by
  unfold ceilingIndex
  split_ifs
  · exact h.le
  · exact Order.succ_le_of_lt h

variable {R : ℕ → Type} {M : Type} {N : Type w} {D : Model R M} {E : Model R N}
local instance : DecidableEq M := Classical.decEq _
variable (F : BackAndForth D E) (C : Presentation R M)

/-- The realizations of a chosen family of pointed source labels over a target tuple. -/
def labelUnion {k} (P : M → Tuple M k → Prop) (t : Tuple N k) : Set N :=
  {y | ∃ x s, P x s ∧ y ∈ orbitFiber F s x t}

include C in
theorem labelUnion_bound {k} (P : M → Tuple M k → Prop) (t : Tuple N k)
    (K : Cardinal.{w}) (hinf : ℵ₀ ≤ K)
    (h : ∀ x s, P x s → #(orbitFiber F s x t) ≤ K) : #(labelUnion F P t) ≤ K := by
  let J := {p : M × Tuple M k // P p.1 p.2}
  let sets (p : J) := orbitFiber F p.1.2 p.1.1 t
  letI : Countable M := Function.Surjective.countable (f := C.enum) C.onto
  have he : labelUnion F P t = ⋃ p, sets p := by
    ext y
    exact ⟨fun ⟨x,s,hp,hy⟩ => mem_iUnion.mpr ⟨⟨(x,s),hp⟩,hy⟩,
      fun hh => let ⟨p,hp⟩ := mem_iUnion.mp hh; ⟨_,_,p.property,hp⟩⟩
  rw [he]
  calc
    #(⋃ p, sets p) ≤ lift.{w} #J * ⨆ p, #(sets p) := by
      simpa only [lift_id'] using mk_iUnion_le_lift sets
    _ ≤ K * K := mul_le_mul' ((show lift.{w} #J ≤ ℵ₀ by simp).trans hinf)
      (ciSup_le' fun p => h _ _ p.property)
    _ = K := mul_eq_self hinf

def earlier {k} (α : Ordinal.{0}) (t : Tuple N k) : Set N :=
  labelUnion F (fun x s => ∃ β < α, ModelOrdinalRankLE D β (List.ofFn s).toFinset x) t

include C in
private theorem earlier_dichotomy {k} (α : Ordinal.{0}) (ha : α ≠ 0)
    (s : Tuple M k) (x : M) (t : Tuple N k)
    (rank : ModelOrdinalRankLE D α (List.ofFn s).toFinset x)
    (inh : (orbitFiber F s x t).Nonempty) :
    (∃ d, orbitFiber F s x t ⊆ earlier F α (push d t)) ∨
    ∀ y ∈ orbitFiber F s x t, ∀ z ∈ orbitFiber F s x t,
      z ∈ earlier F α (push y t) ∨ y ∈ earlier F α (push z t) := by
  unfold ModelOrdinalRankLE at rank
  rw [OrdinalRankLE, if_neg ha] at rank
  rcases rank with ⟨c,hc⟩ | hc
  · left
    obtain ⟨y₀,hy₀⟩ := inh
    obtain ⟨d,hd⟩ := F.closure.forth (hy₀.tail F) c
    refine ⟨d,fun y hy => ?_⟩
    obtain ⟨z,h⟩ := F.closure.back hd y
    obtain ⟨g,hg,hgx⟩ := F.conjugate_of_lifts C hy (h.eraseSecond F)
    obtain ⟨β,hβ,hr⟩ := ordinal_transport_witness g
      (fun a ha => hg a (List.mem_toFinset.mp ha)) hgx hc
    refine ⟨z,push c s,⟨β,hβ,?_⟩,h⟩
    simpa only [ModelOrdinalRankLE, ofFn_push, List.toFinset_cons] using hr
  · right
    intro y hy z hz
    obtain ⟨x',h⟩ := F.closure.back hz y
    obtain ⟨g,hg,hgx⟩ := F.conjugate_of_lifts C hy (h.eraseSecond F)
    rcases hc x' ⟨g,fun a ha => hg a (List.mem_toFinset.mp ha),hgx⟩ with
      ⟨β,hβ,hr⟩ | ⟨β,hβ,hr⟩
    · refine Or.inl ⟨x,push x' s,⟨β,hβ,?_⟩,h.exchange F⟩
      simpa only [ModelOrdinalRankLE,ofFn_push,List.toFinset_cons] using hr
    · refine Or.inr ⟨x',push x s,⟨β,hβ,?_⟩,h⟩
      simpa only [ModelOrdinalRankLE,ofFn_push,List.toFinset_cons] using hr

include C in
/-- The ordinal rank of a pointed orbit bounds its size over arbitrary target parameters. -/
theorem orbitFiber_ordinal_bound (α : Ordinal.{0}) {k} (s : Tuple M k) (x : M) (t : Tuple N k)
    (rank : ModelOrdinalRankLE D α (List.ofFn s).toFinset x) :
    #(orbitFiber F s x t) ≤ lift.{w} (aleph (ceilingIndex α)) := by
  induction α using WellFoundedLT.induction generalizing k s x t with
  | ind α ih =>
    by_cases hfin : α < Ordinal.omega0
    · obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hfin
      have hr := (ordinalRankLE_natCast_iff (G := ↥(automorphismGroup D)) n (List.ofFn s) x).mp rank
      have sub : orbitFiber F s x t ⊆ lowFiber F n t := fun _ hy => ⟨x,s,hr,hy⟩
      simpa [ceilingIndex,hfin] using (mk_le_mk_of_subset sub).trans (lowFiber_cardinal F C n t)
    let K := lift.{w} (aleph α)
    have hinf : ℵ₀ ≤ K := by simp [K]
    have lower {l} (u : Tuple N l) : #(earlier F α u) ≤ K := by
      apply labelUnion_bound F C _ _ K hinf
      rintro v r ⟨β,hβ,hr⟩
      exact (ih β hβ r v u hr).trans (Cardinal.lift_le.mpr
        (aleph_le_aleph.mpr (ceilingIndex_le_of_lt hβ)))
    have ha : α ≠ 0 := fun h => hfin (h ▸ Ordinal.omega0_pos)
    have bound : #(orbitFiber F s x t) ≤ Order.succ K := by
      let O := orbitFiber F s x t
      by_cases inh : O.Nonempty
      · rcases earlier_dichotomy F C α ha s x t rank inh with ⟨d,hd⟩ | cmp
        · exact (mk_le_mk_of_subset hd).trans ((lower _).trans (Order.le_succ _))
        let L (y : O) : Set O := Subtype.val ⁻¹' earlier F α (push y.val t)
        have small (y : O) : #(L y) ≤ K := by
          let f (z : L y) : earlier F α (push y.val t) := ⟨z.val.val,z.property⟩
          have inj : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext
            (congrArg (fun z : earlier F α (push y.val t) => z.val) h))
          exact (mk_le_of_injective inj).trans (lower _)
        exact cardinal_le_succ_of_pair_cover hinf L small
          (fun y z => (cmp _ y.property _ z.property).symm)
      · change #O ≤ _
        simp [Set.not_nonempty_iff_eq_empty.mp inh]
    simpa only [ceilingIndex,if_neg hfin,Order.succ_eq_add_one,← succ_aleph,lift_succ,K] using bound

/-- If every source singleton has a rank whose cardinal bound is at most K,
then every model of its Scott sentence has size at most K. -/
theorem cardinal_le_of_label_bounds {K : Cardinal.{0}} (hinf : ℵ₀ ≤ K)
    (rank : ∀ x, ∃ β, ModelOrdinalRankLE D β ∅ x ∧ aleph (ceilingIndex β) ≤ K)
    (sat : BackAndForth.Satisfies E (C.sentence D)) : #N ≤ lift.{w} K := by
  obtain ⟨F,hf⟩ := (C.satisfies_iff_backAndForth D E).mp sat
  let t : Tuple N 0 := Fin.elim0
  have all : labelUnion F (fun _ _ => True) t = Set.univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x,hx⟩ := F.back hf y
    exact ⟨x,Fin.elim0,trivial,F.lifts_of_match hx⟩
  have h := labelUnion_bound F C (fun _ _ => True) t (lift.{w} K) (by simpa using hinf) (by
    intro x s _
    obtain ⟨β,hr,hK⟩ := rank x
    exact (orbitFiber_ordinal_bound F C β s x t (by simpa using hr)).trans (lift_le.mpr hK))
  simpa only [all,mk_univ] using h

/-- Finite singleton rank n gives ℵₙ. Infinite singleton rank α gives ℵ_(α+1). -/
theorem cardinal_le_of_ordinal_rank (α : Ordinal.{0})
    (rank : ∀ x, ModelOrdinalRankLE D α ∅ x)
    (sat : BackAndForth.Satisfies E (C.sentence D)) : #N ≤ lift.{w} (aleph (ceilingIndex α)) :=
  cardinal_le_of_label_bounds C (aleph0_le_aleph _) (fun x => ⟨α,rank x,le_rfl⟩) sat

/-- At the sharp ceiling, a single orbit attains the bound. At a limit
the conclusion simultaneously excludes every smaller ordinal bound. -/
theorem exists_exact_rank_of_realization (α : Ordinal.{0})
    (rank : ∀ x, ModelOrdinalRankLE D α ∅ x)
    {B : Type} {A : Model R B} (sat : BackAndForth.Satisfies A (C.sentence D))
    (size : #B = aleph (ceilingIndex α)) :
    ∃ x, ModelOrdinalRankLE D α ∅ x ∧ ∀ β < α, ¬ ModelOrdinalRankLE D β ∅ x := by
  by_contra! h
  have smaller (x : M) : ∃ β < α, ModelOrdinalRankLE D β ∅ x := h x (rank x)
  have obstruction (γ : Ordinal.{0}) (hlt : γ < ceilingIndex α)
      (cap : ∀ β < α, ceilingIndex β ≤ γ) : False := by
    have bound := cardinal_le_of_label_bounds C (aleph0_le_aleph γ) (fun x => by
      obtain ⟨β,hβ,hr⟩ := smaller x
      exact ⟨β,hr,aleph_le_aleph.mpr (cap β hβ)⟩) sat
    exact (aleph_lt_aleph.mpr hlt).not_ge (by simpa only [size,lift_id] using bound)
  by_cases hf : α < Ordinal.omega0
  · obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hf
    cases n with
    | zero =>
      obtain ⟨β,hβ,_⟩ := smaller (C.enum 0)
      simp at hβ
    | succ n =>
      apply obstruction n
      · rw [ceilingIndex,if_pos hf]
        exact Nat.cast_lt.mpr (Nat.lt_succ_self n)
      · intro β hβ
        rw [ceilingIndex,if_pos (hβ.trans hf)]
        exact Order.lt_succ_iff.mp (by simpa only [Order.succ_eq_add_one,Nat.cast_succ] using hβ)
  · apply obstruction α
    · rw [ceilingIndex,if_neg hf]
      exact Order.lt_succ _
    · exact fun _ hβ => ceilingIndex_le_of_lt hβ

end
end KnightModel.Transfinite
