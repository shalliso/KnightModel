import KnightModel.RankTwo.ProgramDefinabilityComposites
import KnightModel.RankTwo.RankWordPrimitives

/-! # Compiling the whole coordinate grammar from the two interval operations -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I] (i : I)

theorem all_schemes_of_intervals
    (interval : ∀ m n, SchemeDefinable i (.interval m n))
    (tail : ∀ n, SchemeDefinable i (.tail n)) : ∀ k, SchemeDefinable i k := by
  intro k
  induction k with
  | id => exact schemeDefinable_id i
  | empty => exact schemeDefinable_empty i
  | «prefix» n => exact schemeDefinable_prefix i n
  | through n => exact schemeDefinable_through i n
  | interval m n => exact interval m n
  | tail n => exact tail n
  | atMost n => exact schemeDefinable_atMost i n
  | above n => exact schemeDefinable_above i n
  | seq f g hf hg => exact SchemeDefinable.seq i hf hg
  | union f g hf hg => exact SchemeDefinable.union i hf hg
  | inv f hf => exact SchemeDefinable.inv i hf

theorem definable_run_of_schemes (hs : ∀ k, SchemeDefinable i k)
    {n} (k : Name n) (c : Code i) :
    Definable {v : Fin n → VectorGroup I | run i k (Sum.inr ∘ v) = some c} := by
  apply definable_run_fiber i _ (fun l => ⟨l.val.graphBound,concrete_graph_bound i l⟩)
  rintro m ⟨l,rfl⟩
  exact hs l

end KnightModel.RankTwo.Concrete
