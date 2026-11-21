import KnightModel.RankTwo.ScottRestrictionMotions

/-! # Definable dependence and finite stage partitions in an arbitrary Scott model -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Restriction

variable {R : ℕ → Type u} {M N : Type} {C : Presentation R M} {D : Model R M} {E : Model R N}
    {h : BackAndForth.Satisfies E (C.sentence D)}

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

/-- The unique-realization property of rank zero transfers to any second
realization of the same label over the identical target base. -/
theorem unique_by_zero {n} {t : Tuple N n} {x y : N} (hx : x ∈ lowFiber F 0 t)
    (eqn : (L).label (push x t) = (L).label (push y t)) : x = y := by
  obtain ⟨a,s,ra,hx⟩ := hx
  have hy : (F).Lifts (push a s) (push y t) := (lifts_iff C D E h _ _).mpr
    (((number_eq_iff C D E h _ _).mp eqn _).mp ((lifts_iff C D E h _ _).mp hx))
  obtain ⟨b,hb⟩ := (F).closure.back hx y
  obtain ⟨g,hg,ha⟩ := (F).conjugate_of_lifts C hy (hb.eraseSecond F)
  have ab : a = b := (ra g hg).symm.trans ha
  exact ((hb.head_eq F).mp ab.symm).symm

theorem dependent_point_fixed {n} {t : Tuple N n} {x y : N} (hx : x ∈ lowFiber F 0 t)
    {f : (L).Motion} (fix : ∀ j, f.Mem (t j) (t j)) (xy : f.Mem x y) : x = y :=
  unique_by_zero hx <| f.same_of_mems (Fin.cases xy fix)

/-- Low relative ranks persist after adjoining any finite list of extra points
to the front of the base. This is a statement about actual target fibers. -/
theorem lowFiber_cons {n k} {t : Tuple N k} {x : N} (hx : x ∈ lowFiber F n t) (z : N) :
    x ∈ lowFiber F n (push z t) := by
  obtain ⟨a,s,ra,hs⟩ := hx
  obtain ⟨b,hb⟩ := (F).closure.back hs z
  exact ⟨a,push b s,ofFn_push b s ▸ (ra.mono_params fun v hv => List.mem_cons_of_mem b hv),
    hb.exchange F⟩

/-- Fixing the later point and the base forces any earlier definable point to
remain fixed after a one-point extension of the finite correspondence. -/
theorem refine_over {t : List N} {a b : N} (ha : a ∈ lowFiber F 0 (push b t.get))
    {u v : List N} (hm : (L).Over (b::t) u v) : (L).Over (a::t) u v := by
  obtain ⟨f,hf,hw⟩ := hm
  obtain ⟨g,z,hz,inc⟩ := f.extend_point a
  have fix : ∀ j : Fin (t.length+1), g.Mem (push b t.get j) (push b t.get j) :=
    Fin.cases (inc _ _ (hf b List.mem_cons_self))
      (fun j => inc _ _ (hf _ (List.mem_cons_of_mem _ (List.get_mem _ _))))
  obtain rfl := dependent_point_fixed ha fix hz
  refine ⟨g,?_,hw.imp inc⟩
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hz
  · exact inc _ _ (hf v (List.mem_cons_of_mem _ hv))

/-- The partitions used in stabilization are literal equality of complete
Scott labels over the base and the stage point. -/
noncomputable def stagePartitions {ι : Type} (S : Stages ι) (base : List N) (a : ι → N)
    (chain : ∀ i j, S.le i j → a i ∈ lowFiber F 0 (push (a j) base.get)) :
    TuplePartitions S N where
  ambient := (L).overSetoid base
  atStage i := (L).overSetoid (a i::base)
  refinesAmbient i _ _ hm := by
    obtain ⟨f,hf,hv⟩ := hm
    exact ⟨f,fun x hx => hf x (List.mem_cons_of_mem _ hx),hv⟩
  refine i j hij _ _ := refine_over (chain i j hij)
  length_eq _ _ _ := (L).over_length
  forgetHead _ _ _ _ _ := (L).over_forgetHead
  liftHead _ _ _ := (L).over_liftHead

/-- If each entry of a finite tuple is determined by the coordinates already
fixed by a motion, one finite extension fixes the entire tuple. -/
theorem fix_dependent_list (b w : List N)
    (dep : ∀ x ∈ w, x ∈ lowFiber F 0 b.get)
    (f : (L).Motion) (fixed : f.Fixes b) :
    ∃ g : (L).Motion, (∀ x y, f.Mem x y → g.Mem x y) ∧ g.Fixes w := by
  induction w generalizing f with
  | nil => exact ⟨f,fun _ _ hx => hx,fun _ hx => (List.not_mem_nil hx).elim⟩
  | cons x w ih =>
    obtain ⟨g,z,zx,inc⟩ := f.extend_point x
    have fixed' : g.Fixes b := fun v hv => inc _ _ (fixed v hv)
    obtain rfl := dependent_point_fixed (dep x List.mem_cons_self)
      (fun i => fixed' _ (List.get_mem _ i)) zx
    obtain ⟨l,inc',fixw⟩ := ih (fun v hv => dep _ (List.mem_cons_of_mem _ hv)) g fixed'
    refine ⟨l,fun _ _ hy => inc' _ _ (inc _ _ hy),fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact inc' _ _ zx
    · exact fixw v hv

/-- Stage partitions for arbitrary finite tuples of parameters. The only
ordering requirement is that earlier definable coordinates remain fixed. -/
noncomputable def collectionPartitions {ι : Type} (S : Stages ι) (base : List N) (a : ι → List N)
    (refinement : ∀ i j, S.le i j → ∀ u v,
      (L).Over (a j ++ base) u v → (L).Over (a i ++ base) u v) :
    TuplePartitions S N where
  ambient := (L).overSetoid base
  atStage i := (L).overSetoid (a i ++ base)
  refinesAmbient i _ _ h' := by
    obtain ⟨f,fix,hw⟩ := h'
    exact ⟨f,fun x hx => fix _ (List.mem_append_right _ hx),hw⟩
  refine := refinement
  length_eq _ _ _ := (L).over_length
  forgetHead _ _ _ _ _ := (L).over_forgetHead
  liftHead _ _ _ := (L).over_liftHead

theorem list_stage_refinement {ι : Type} (S : Stages ι) (B : List N) (a : ι → List N)
    (chain : ∀ i j, S.le i j → ∀ x ∈ a i, x ∈ lowFiber F 0 (a j ++ B).get)
    (i j : ι) (hij : S.le i j) (u v : List N) (h' : (L).Over (a j ++ B) u v) :
    (L).Over (a i ++ B) u v := by
  obtain ⟨f,fixed,hw⟩ := h'
  obtain ⟨g,inc,fixw⟩ := fix_dependent_list (a j ++ B) (a i) (chain i j hij) f fixed
  refine ⟨g,?_,hw.imp inc⟩
  intro x hx
  rcases List.mem_append.mp hx with ha | hb
  · exact fixw x ha
  · exact inc _ _ (fixed _ (List.mem_append_right _ hb))

namespace Labels

variable {X : Type} (T : Labels X)

theorem over_head_iff {B w : List X} {x y : X} :
    T.Over B (x::w) (y::w) ↔ ∃ f : T.Motion, f.Fixes (w++B) ∧ f.Mem x y := by
  constructor
  · rintro ⟨f,hf,hw⟩
    cases hw with
    | cons h hs =>
      refine ⟨f,fun z hz => ?_,h⟩
      rcases List.mem_append.mp hz with hz | hz
      · exact List.forall₂_same.mp hs z hz
      · exact hf z hz
  · rintro ⟨f,hf,h⟩
    exact ⟨f,fun z hz => hf _ (List.mem_append_right _ hz),
      .cons h (List.forall₂_same.mpr fun z hz => hf _ (List.mem_append_left _ hz))⟩

theorem one_over_iff {B : List X} {x y : X} :
    (∃ f : T.Motion, f.Fixes B ∧ f.Mem x y) ↔
      T.label (push x B.get) = T.label (push y B.get) := by
  constructor
  · rintro ⟨f,hf,h⟩
    exact f.same_of_mems (Fin.cases h (fun j => hf _ (List.get_mem _ j)))
  · intro he
    let f : T.Motion := ⟨_,push x B.get,push y B.get,he⟩
    refine ⟨f,?_,⟨0,rfl,rfl⟩⟩
    intro z hz
    obtain ⟨i,hi⟩ := List.get_of_mem hz
    exact ⟨i.succ,hi,hi⟩

/-- Complete labels for tuples over a finite base are equivalent precisely
when one finite elementary motion can match their coordinates and fix the base. -/
theorem tuple_over_iff {B : List X} {m : Nat} {x y : Tuple X m} :
    (∃ f : T.Motion, f.Fixes B ∧ ∀ i, f.Mem (x i) (y i)) ↔
      T.label (Fin.addCases x B.get) = T.label (Fin.addCases y B.get) := by
  constructor
  · rintro ⟨f,hb,hxy⟩
    apply f.same_of_mems
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hxy j
    · simpa only [Fin.addCases_right] using hb _ (List.get_mem _ j)
  · intro he
    let f : T.Motion := ⟨_,Fin.addCases x B.get,Fin.addCases y B.get,he⟩
    refine ⟨f,?_,?_⟩
    · intro z hz
      obtain ⟨j,hj⟩ := List.get_of_mem hz
      refine ⟨Fin.natAdd m j, ?_, ?_⟩ <;> simpa [f] using hj
    · intro j
      refine ⟨Fin.castAdd B.length j, ?_, ?_⟩ <;> simp [f]

end Labels
end KnightModel.RankTwo.Scott.SentenceLabels
