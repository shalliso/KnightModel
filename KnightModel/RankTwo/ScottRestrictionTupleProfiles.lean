import KnightModel.RankTwo.ScottRestrictionProfiles

/-! # Countable simultaneous profiles of finite-tuples along a dependence chain -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Restriction Set

namespace Labels

variable {X : Type} (L : Labels X)

def tupleJoint {m} (x : Tuple X m) (u : List X) := L.label (Fin.addCases x u.get)

private theorem addCases_cast {m n k : ℕ} (he : n = k) (x : Tuple X m) (t : Tuple X k) :
    L.label (Fin.addCases x (t ∘ Fin.cast he)) = L.label (Fin.addCases x t) := by
  subst k
  rfl

theorem tupleJoint_ofFn {m n} (x : Tuple X m) (t : Tuple X n) :
    L.tupleJoint x (List.ofFn t) = L.label (Fin.addCases x t) := by
  have he : (List.ofFn t).get = t ∘ Fin.cast (List.length_ofFn (f := t)) :=
    funext fun j => List.get_ofFn t j
  exact (congrArg (fun q => L.label (Fin.addCases x q)) he).trans (L.addCases_cast _ _ _)

theorem tupleJoint_of_motion {f : L.Motion} {m} {x y : Tuple X m} (hxy : ∀ j, f.Mem (x j) (y j))
    {u v : List X} (hv : List.Forall₂ f.Mem u v) : L.tupleJoint x u = L.tupleJoint y v := by
  have he := hv.length_eq
  have hp (j : Fin u.length) : f.Mem (u.get j) ((v.get ∘ Fin.cast he) j) :=
    hv.get j.isLt (Fin.cast he j).isLt
  apply Eq.trans _ (L.addCases_cast he y v.get)
  apply f.same_of_mems
  intro j
  cases j using Fin.addCases with
  | left j => simpa only [Fin.addCases_left] using hxy j
  | right j => simpa only [Fin.addCases_right] using hp j

end Labels

variable {R : ℕ → Type u} {M N : Type} (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D))

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

/-- The finite-tuple version, with all earlier coordinates determined by
the later tuple over the fixed base. Only the inserted parameters need rank one. -/
theorem chain_tuple_profiles (base : List N) {m} (y : OmegaOne → Tuple N m)
    (chain : ∀ i j, i ≤ j → ∀ l, y i l ∈ lowFiber F 0 ((List.ofFn (y j)) ++ base).get)
    {A : Type} [Countable A] (z : A → N) (low : ∀ a, z a ∈ lowFiber F 1 base.get) :
    (range (fun i : OmegaOne => fun u : Sigma (Tuple A) =>
      number C D E h (Fin.addCases (y i) (fun l => z (u.2 l))))).Countable := by
  classical
  haveI : Nonempty (Sigma (Tuple A)) := ⟨⟨0,Fin.elim0⟩⟩
  obtain ⟨e, onto⟩ := exists_surjective_nat (Sigma (Tuple A))
  let stage (i : OmegaOne) := List.ofFn (y i)
  have chain' (i j : OmegaOne) (hij : i ≤ j) (x : N) (hx : x ∈ stage i) :
      x ∈ lowFiber F 0 (stage j ++ base).get := by
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hx
    exact chain i j hij l
  let refines := list_stage_refinement omegaOneStages base stage chain'
  let T := collectionPartitions omegaOneStages base stage refines
  let params (n : Nat) := List.ofFn (fun j => z ((e n).2 j))
  let label (i j : OmegaOne) := (L).tupleJoint (y j) (stage i ++ base)
  let joint (i : OmegaOne) := (L).tupleJoint (y i)
  have hparam (n : Nat) (x : N) (hx : x ∈ params n) : x ∈ lowFiber F 1 base.get := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact low _
  have readout (i : OmegaOne) (u v : List N) (q : (T.atStage i).r u v) : joint i u = joint i v := by
    obtain ⟨f,fix,uv⟩ := q
    exact (L).tupleJoint_of_motion (fun j => fix _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩))) uv
  have transport (i j k : OmegaOne) (_ : i ≤ j) (_ : i ≤ k) (eq : label i j = label i k)
      (u : List N) : ∃ v, (T.atStage i).r v u ∧ joint j u = joint k v := by
    let s := stage i ++ base
    let src : Tuple N (m+s.length) := Fin.addCases (y j) s.get
    let dst : Tuple N (m+s.length) := Fin.addCases (y k) s.get
    let f : (L).Motion := ⟨m+s.length,src,dst,show (L).label src = (L).label dst from eq⟩
    have fix (x : N) (hx : x ∈ s) : f.Mem x x := by
      obtain ⟨r,hr⟩ := List.get_of_mem hx
      exact ⟨r.natAdd m,by simpa [f,src,dst] using hr,by simpa [f,src,dst] using hr⟩
    have move (r : Fin m) : f.Mem (y j r) (y k r) :=
      ⟨r.castAdd s.length, by simp [f,src], by simp [f,dst]⟩
    obtain ⟨g,v,uv,ext⟩ := f.extend_list L u
    have q : (L).Over (stage i ++ base) u v := ⟨g,fun b hb => ext _ _ (fix b hb),uv⟩
    exact ⟨v,(L).over_symm q,(L).tupleJoint_of_motion (fun r => ext _ _ (move r)) uv⟩
  obtain ⟨i,stabilizes⟩ := countable_profile_factorization omegaOneStages T
    (· ∈ lowFiber F 1 base.get) (fun a ha w _ => collection_lowOver omegaOneStages base stage refines ha w)
    params hparam label joint readout transport
  let profile (k : OmegaOne) (u : Sigma (Tuple A)) :=
    number C D E h (Fin.addCases (y k) (fun l => z (u.2 l)))
  have cover := countable_range_of_tail_labels omegaOneStages omegaOne_initial profile label
    ⟨i,by
      intro j k hj hk he
      funext u
      obtain ⟨n,rfl⟩ := onto u
      exact ((L).tupleJoint_ofFn _ _).symm.trans
        ((stabilizes j k hj hk he n).trans ((L).tupleJoint_ofFn _ _))⟩
  obtain ⟨f,hf⟩ := cover
  exact countable_iff_exists_subset_range.mpr ⟨f,fun _ hp => hf _ hp⟩

end KnightModel.RankTwo.Scott.SentenceLabels
