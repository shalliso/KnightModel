import KnightModel.RankTwo.ScottRestrictionOperators

/-! # Rank-one stabilization for genuine Scott labels -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Set Cardinal Restriction

variable {R : ℕ → Type u} {M N : Type} {C : Presentation R M} {D : Model R M} {E : Model R N}
    {h : BackAndForth.Satisfies E (C.sentence D)}

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

theorem lowFiber_prepend_list {n} {B : List N} {x : N} (hx : x ∈ lowFiber F n B.get) (w : List N) :
    x ∈ lowFiber F n (w ++ B).get := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have he : ((a::w)++B).get = push a (w++B).get := funext (Fin.cases rfl (fun _ => rfl))
    rw [he]
    exact lowFiber_cons ih a

/-- At any further finite base the one-point partition satisfies the actual
rank-one alternatives. In the comparison case the witnesses are explicit
maps indexed by the natural numbers, one for each complete pointed label. -/
theorem collection_lowOver {ι : Type} (S : Stages ι) (B : List N) (a : ι → List N)
    (refinement : ∀ i j, S.le i j → ∀ u v,
      (L).Over (a j ++ B) u v → (L).Over (a i ++ B) u v)
    {z : N} (hz : z ∈ lowFiber F 1 B.get) (w : List N) :
    (collectionPartitions S B a refinement).lowOver w z := by
  classical
  let b := w ++ B
  let O : Set N := {x | (L).Over B (x::w) (z::w)}
  have inO (x : N) : x ∈ O ↔ (L).label (push x b.get) = (L).label (push z b.get) :=
    ((L).over_head_iff).trans ((L).one_over_iff)
  have hzO : z ∈ O := (inO z).mpr rfl
  have hzb : z ∈ lowFiber F 1 b.get := lowFiber_prepend_list hz w
  obtain ⟨v,s,rank,hlift⟩ := hzb
  have labelz := (lifts_iff C D E h _ _).mp hlift
  have Oeq : O = orbitFiber F s v b.get := by
    ext x
    rw [inO x]
    change (L).label (push x b.get) = (L).label (push z b.get) ↔ (F).Lifts (push v s) (push x b.get)
    rw [lifts_iff]
    constructor
    · intro eqn
      exact (((number_eq_iff C D E h _ _).mp eqn) _).mpr labelz
    · intro hx
      exact (number_eq_iff C D E h _ _).mpr (theory_of_label C D E h hx labelz)
  rcases orbitFiber_dichotomy F C s v b.get rank ⟨z,hlift⟩ with ⟨d,small⟩ | compare
  · apply Or.inl
    have small' : #O ≤ ℵ₀ := by
      rw [Oeq]
      exact (mk_le_mk_of_subset small).trans (by simpa using lowFiber_cardinal F C 0 (push d b.get))
    letI : Countable O := mk_le_aleph0_iff.mp small'
    letI : Nonempty O := ⟨⟨z,hzO⟩⟩
    obtain ⟨f,hf⟩ := countable_iff_exists_surjective.mp (inferInstance : Countable O)
    exact ⟨f,fun x _ => hf x⟩
  · have stable (g : (L).Motion) (fixed : ∀ i, g.Mem (b.get i) (b.get i))
        (x : N) (hx : x ∈ O) (y : N) (xy : g.Mem x y) : y ∈ O := by
      have num := g.same_of_mems (s := push x b.get) (t := push y b.get) (Fin.cases xy fixed)
      exact (inO y).mpr (num.symm.trans ((inO x).mp hx))
    apply Or.inr
    refine ⟨orbitalMap (h := h) b.get O,fun x y => ?_,?_⟩
    · exact orbitalMap_compare (compare y.val (Oeq ▸ y.property) x.val (Oeq ▸ x.property))
    · intro i k x y hmatch
      have m : (L).Over (a i++B) (x.val::w) (y.val::w) := hmatch
      obtain ⟨f,hf,hxy⟩ := (L).over_head_iff.mp m
      have fix (j : Fin b.length) : f.Mem (b.get j) (b.get j) := by
        apply hf
        have hj : b.get j ∈ w ++ B := List.get_mem _ _
        rcases List.mem_append.mp hj with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_right _ h)
      obtain ⟨g,inc,hw⟩ := orbitalMap_move stable k (x := x) (y := y) f fix hxy
      exact (L).over_head_iff.mpr ⟨g,fun u hu => inc _ _ (hf u hu),hw⟩

/-- The specialization for stages represented by just one parameter. -/
theorem stage_lowOver {ι : Type} (S : Stages ι) (B : List N) (a : ι → N)
    (chain : ∀ i j, S.le i j → a i ∈ lowFiber F 0 (push (a j) B.get))
    {z : N} (hz : z ∈ lowFiber F 1 B.get) (w : List N) :
    (stagePartitions S B a chain).lowOver w z :=
  collection_lowOver S B (fun i => [a i])
    (fun i j hij _ _ hm => refine_over (chain i j hij) hm) hz w

/-- Tuple stabilization with any finite number of parameters at each stage,
with no common bound on their lengths. -/
theorem scott_tuple_stages_stabilize {ι : Type} (S : Stages ι) (B : List N) (a : ι → List N)
    (chain : ∀ i j, S.le i j → ∀ x ∈ a i, x ∈ lowFiber F 0 (a j ++ B).get)
    (w : List N) (hw : ∀ x ∈ w, x ∈ lowFiber F 1 B.get) :
    ∃ i, ∀ j, S.le i j → ∀ v, (L).Over (a i ++ B) v w ↔ (L).Over (a j ++ B) v w :=
  tuple_cell_stabilizes S (collectionPartitions S B a (list_stage_refinement S B a chain))
    (· ∈ lowFiber F 1 B.get)
    (fun _ hz u _ => collection_lowOver S B a (list_stage_refinement S B a chain) hz u) w hw

/-- The whole finite tuple of lower-rank parameters stabilizes, including
the comparison and witness alternatives at each point. -/
theorem scott_tuple_cell_stabilizes {ι : Type} (S : Stages ι) (B : List N) (a : ι → N)
    (chain : ∀ i j, S.le i j → a i ∈ lowFiber F 0 (push (a j) B.get))
    (w : List N) (hw : ∀ x ∈ w, x ∈ lowFiber F 1 B.get) :
    ∃ i, ∀ j, S.le i j → ∀ v,
      (L).Over (a i::B) v w ↔ (L).Over (a j::B) v w :=
  tuple_cell_stabilizes S (stagePartitions S B a chain) (· ∈ lowFiber F 1 B.get)
    (fun _ hz u _ => stage_lowOver S B a chain hz u) w hw

end KnightModel.RankTwo.Scott.SentenceLabels
