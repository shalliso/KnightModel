import KnightModel.RankTwo.ScottRestrictionStabilization
import KnightModel.RankTwo.RestrictionOrdinal

/-! # Stabilization over an increasing ω₁-sequence of finite tuples -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Restriction

variable {R : ℕ → Type u} {M N : Type} {C : Presentation R M} {D : Model R M} {E : Model R N}
    {h : BackAndForth.Satisfies E (C.sentence D)}

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

/-- Every coordinate named in a target tuple has rank zero over that tuple. -/
theorem named_coordinate_zero {n} (t : Tuple N n) (j : Fin n) : t j ∈ lowFiber F 0 t := by
  obtain ⟨s,hs⟩ := exists_label C D E h t
  have lift := (lifts_iff C D E h s t).mpr hs
  let p : Fin (n+1) → Fin n := Fin.cases j id
  have s' : s ∘ p = push (s j) s := funext (Fin.cases rfl (fun _ => rfl))
  have t' : t ∘ p = push (t j) t := funext (Fin.cases rfl (fun _ => rfl))
  refine ⟨s j,s,fun g hg => hg _ (List.mem_ofFn.mpr ⟨j,rfl⟩),?_⟩
  change (F).Lifts (push (s j) s) (push (t j) t)
  simpa only [s',t'] using lift.select _ p

/-- The finite parameter tuple may have different lengths at different
stages. Dependence is needed only for strictly earlier stages. -/
theorem omegaOne_tuple_stages_stabilize (B : List N) (a : OmegaOne → List N)
    (chain : ∀ i j, i < j → ∀ x ∈ a i, x ∈ lowFiber F 0 (a j ++ B).get)
    (w : List N) (hw : ∀ x ∈ w, x ∈ lowFiber F 1 B.get) :
    ∃ i, ∀ j ≥ i, ∀ v, (L).Over (a i ++ B) v w ↔ (L).Over (a j ++ B) v w := by
  apply scott_tuple_stages_stabilize omegaOneStages B a _ w hw
  intro i j hij x hx
  rcases (show i ≤ j from hij).lt_or_eq with lt | rfl
  · exact chain i j lt x hx
  · obtain ⟨k,hk⟩ := List.get_of_mem (List.mem_append_left B hx)
    exact hk ▸ named_coordinate_zero (a i ++ B).get k

end KnightModel.RankTwo.Scott.SentenceLabels
