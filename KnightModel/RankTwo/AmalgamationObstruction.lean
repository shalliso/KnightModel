import KnightModel.RankTwo.AmalgamationTwists
import KnightModel.RankTwo.AmalgamationNecessity

/-! # Countable amalgamation fails in every rank-two positive example -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal Set

variable {R : ℕ → Type} {M N : Type} {D : Model R M} {E : Model R N}

/-- If the Scott sentence of a singleton-rank-at-most-two model has an ℵ₂-sized
model, the countable model admits a single proper elementary self-extension
with continuum many pairwise nonamalgamable twists. -/
theorem continuum_incompatible_of_large_model (C : Presentation R M)
    (sat : BackAndForth.Satisfies E (C.sentence D)) (size : aleph 2 ≤ #N)
    (rank : ∀ x, ModelRankLE D 2 [] x) :
    ∃ (ι : Elementary D D) (b x : M) (f : (ℕ → Bool) ↪ automorphismGroup D),
      x ∉ range ι ∧ ModelRankLE D 1 [ι b] x ∧
      (∀ a, (f a).val b = b) ∧ Pairwise (fun a c => ¬ Amalgamates C D D ι (f a) (f c)) := by
  obtain ⟨ι,b,x,hx,hr⟩ := new_rank_one_extension C sat size rank
  let B := Negative.singleton b
  have base : List.ofFn (ι ∘ B) = [ι b] := by
    rw [List.ofFn_succ]
    rfl
  have low : ModelRankLE D 1 (List.ofFn (ι ∘ B)) x := base ▸ hr
  obtain ⟨f,hf,ha⟩ := continuum_twists_of_new_rank_one C D D ι C B x
    (fun y h => hx ⟨y,h⟩) low
  exact ⟨ι,b,x,f,hx,hr,(fun a => hf a _ (List.mem_ofFn.mpr ⟨0,rfl⟩)),ha⟩

end KnightModel.RankTwo.Scott.MarkedExtension
