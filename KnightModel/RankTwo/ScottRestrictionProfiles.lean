import KnightModel.RankTwo.ScottRestrictionStabilization
import KnightModel.RankTwo.RestrictionOrdinal

/-! # Actual Scott diagrams on rank-one chains over countably many parameters -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Restriction Set

namespace Labels

variable {X : Type} (L : Labels X)

theorem Motion.extend_list (f : L.Motion) (u : List X) :
    ∃ (g : L.Motion) (v : List X), List.Forall₂ g.Mem u v ∧
      ∀ x y, f.Mem x y → g.Mem x y := by
  induction u generalizing f with
  | nil => exact ⟨f,[],.nil,fun _ _ h => h⟩
  | cons x u ih =>
    obtain ⟨f', x', hx, extend⟩ := f.extend_point x
    obtain ⟨g,v,hv,ext⟩ := ih f'
    exact ⟨g,x'::v,.cons (ext _ _ hx) hv,fun _ _ h => ext _ _ (extend _ _ h)⟩

/-- The numeric label of a single point together with a variable-length word
of parameters, with arity given by the length of that word. -/
def joint (x : X) (u : List X) := L.label (push x u.get)

private theorem push_cast {n m : ℕ} (he : n = m) (x : X) (t : Tuple X m) :
    L.label (push x (t ∘ Fin.cast he)) = L.label (push x t) := by
  subst m
  rfl

theorem joint_ofFn {n} (x : X) (t : Tuple X n) :
    L.joint x (List.ofFn t) = L.label (push x t) := by
  have he : (List.ofFn t).get = t ∘ Fin.cast (List.length_ofFn (f := t)) :=
    funext fun j => List.get_ofFn t j
  exact (congrArg (fun q => L.label (push x q)) he).trans (L.push_cast _ _ _)

theorem joint_of_motion {f : L.Motion} {x y : X} (hxy : f.Mem x y)
    {u v : List X} (hv : List.Forall₂ f.Mem u v) : L.joint x u = L.joint y v := by
  have he := hv.length_eq
  have hp (j : Fin u.length) : f.Mem (u.get j) ((v.get ∘ Fin.cast he) j) :=
    hv.get j.isLt (Fin.cast he j).isLt
  exact (f.same_of_mems (s := push x u.get) (t := push y (v.get ∘ Fin.cast he))
    (Fin.cases hxy hp)).trans (L.push_cast he _ _)

end Labels

variable {R : ℕ → Type u} {M N : Type} (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D))

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

/-- Once the low-over-base hypothesis is expressed by the stage partitions,
all finite diagrams on a countable set have only countably many simultaneous
values along an omega-one chain of mutually dependent points. -/
theorem chain_profiles_of_lowOver (base : List N) (y : OmegaOne → N)
    (chain : ∀ i j, i ≤ j → y i ∈ lowFiber F 0 (push (y j) base.get))
    {A : Type} [Countable A] (z : A → N)
    (low : ∀ a, a ∈ range z → ∀ w : List N, (stagePartitions omegaOneStages base y chain).lowOver w a) :
    (range (fun i : OmegaOne => fun u : Sigma (Tuple A) =>
      number C D E h (push (y i) (fun l => z (u.2 l))))).Countable := by
  classical
  haveI : Nonempty (Sigma (Tuple A)) := ⟨⟨0,Fin.elim0⟩⟩
  obtain ⟨e, onto⟩ := exists_surjective_nat (Sigma (Tuple A))
  let T := stagePartitions omegaOneStages base y chain
  let params (n : Nat) := List.ofFn (fun j => z ((e n).2 j))
  let label (i j : OmegaOne) := (L).label (push (y j) (y i :: base).get)
  let joint (i : OmegaOne) := (L).joint (y i)
  have hparam (n : Nat) (x : N) (hx : x ∈ params n) : x ∈ range z := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact mem_range_self _
  have readout (i : OmegaOne) (u v : List N) (q : (T.atStage i).r u v) : joint i u = joint i v := by
    obtain ⟨f,fix,uv⟩ := q
    exact (L).joint_of_motion (fix _ List.mem_cons_self) uv
  have transport (i j k : OmegaOne) (_ : i ≤ j) (_ : i ≤ k) (eq : label i j = label i k)
      (u : List N) : ∃ v, (T.atStage i).r v u ∧ joint j u = joint k v := by
    obtain ⟨f,fix,hjk⟩ := ((L).one_over_iff).mpr eq
    obtain ⟨g,v,uv,ext⟩ := f.extend_list L u
    have q : (L).Over (y i :: base) u v := ⟨g,fun b hb => ext _ _ (fix b hb),uv⟩
    exact ⟨v,(L).over_symm q,(L).joint_of_motion (ext _ _ hjk) uv⟩
  obtain ⟨i,stabilizes⟩ := countable_profile_factorization omegaOneStages T
    (fun x => x ∈ range z) (fun a ha w _ => low a ha w) params hparam label joint readout transport
  let profile (k : OmegaOne) (u : Sigma (Tuple A)) :=
    number C D E h (push (y k) (fun l => z (u.2 l)))
  have cover := countable_range_of_tail_labels omegaOneStages omegaOne_initial profile label
    ⟨i,by
      intro j k hj hk he
      funext u
      obtain ⟨n,rfl⟩ := onto u
      exact ((L).joint_ofFn _ _).symm.trans
        ((stabilizes j k hj hk he n).trans ((L).joint_ofFn _ _))⟩
  obtain ⟨f,hf⟩ := cover
  exact countable_iff_exists_subset_range.mpr ⟨f,fun _ hp => hf _ hp⟩

/-- Countable finite-tuple diagrams on every actual rank-one chain over its finite base. -/
theorem chain_profiles (base : List N) (y : OmegaOne → N)
    (chain : ∀ i j, i ≤ j → y i ∈ lowFiber F 0 (push (y j) base.get))
    {A : Type} [Countable A] (z : A → N) (low : ∀ a, z a ∈ lowFiber F 1 base.get) :
    (range (fun i : OmegaOne => fun u : Sigma (Tuple A) =>
      number C D E h (push (y i) (fun l => z (u.2 l))))).Countable := by
  apply chain_profiles_of_lowOver C D E h base y chain z
  rintro _ ⟨a,rfl⟩ w
  exact stage_lowOver omegaOneStages base y chain (low a) w

end KnightModel.RankTwo.Scott.SentenceLabels
