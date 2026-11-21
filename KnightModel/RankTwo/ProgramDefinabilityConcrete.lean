import KnightModel.RankTwo.ConcreteModel
import KnightModel.RankTwo.ProgramDefinabilityLift
import KnightModel.RankTwo.VectorSampling

/-! # Semilinear fibers of the named transition relation -/

namespace KnightModel.RankTwo.Concrete

open Semilinear

variable {I : Type} [LinearOrder I]

/-- Word graph of a named scheme, requiring valid nonnegative vector
parameters. A tuple containing a negative parameter gives the empty graph. -/
def schemeGraph {n} (i : I) (k : Name n) (v : Fin n → VectorGroup I)
    (x y : List (Letter I)) : Prop :=
  ∃ t : Fin n → Letter I, (∀ j, (t j).val = v j) ∧
    k.val.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter
      (List.ofFn t) x y

theorem schemeGraph_letters {n} (i : I) (k : Name n) (t : Fin n → Letter I) (x y : List (Letter I)) :
    schemeGraph i k (fun j => (t j).val) x y ↔
      k.val.Rel Word.shiftLetter ⟨0,le_rfl⟩ (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter
        (List.ofFn t) x y := by
  refine ⟨fun ⟨t', he, h⟩ => ?_, fun h => ⟨t,fun _ => rfl,h⟩⟩
  obtain rfl : t' = t := funext fun j => Subtype.ext (he j)
  exact h

/-- Equality with one fixed coordinate certifies admissibility of the tuple by
testing the image of the root. Thus the fiber needs no separate validity test on
all other parameter values. -/
theorem run_vectors_iff {n} (i : I) (k : Name n) (v : Fin n → VectorGroup I) (c : Code i) :
    run i k (Sum.inr ∘ v) = some c ↔ ∀ x y, schemeGraph i k v x y ↔ c.val x = y := by
  rw [run_eq_some]
  constructor
  · rintro ⟨t, he, g⟩
    have h : v = fun j => (t j).val := funext fun j => Sum.inr.inj (he j)
    subst v
    intro x y
    exact (schemeGraph_letters i k t _ _).trans (g x y)
  · intro agree
    obtain ⟨t, he, _⟩ := (agree [] (c.val [])).mpr rfl
    obtain rfl : v = fun j => (t j).val := funext fun j => (he j).symm
    refine ⟨t,fun _ => rfl, fun x y => ?_⟩
    exact (schemeGraph_letters i k t _ _).symm.trans (agree x y)

/-- The bound only has to be proved on legitimate parameter tuples. -/
theorem schemeGraph_bounds {n} (i : I) (k : Name n) (b : Nat)
    (h : ∀ t : Fin n → Letter I, PrefixBounds (k.val.Rel Word.shiftLetter ⟨0,le_rfl⟩
      (unitLetter i) (zero_lt_unit i) Word.shiftOpenLetter (List.ofFn t)) b)
    (v : Fin n → VectorGroup I) : PrefixBounds (schemeGraph i k v) b := by
  by_cases valid : ∃ t : Fin n → Letter I, ∀ j, (t j).val = v j
  · obtain ⟨t,ht⟩ := valid
    obtain rfl : v = fun j => (t j).val := funext fun j => (ht j).symm
    have he := funext₂ fun x y => propext (schemeGraph_letters i k t x y)
    exact he ▸ h t
  · have he : schemeGraph i k v = (fun _ _ => False) := by
      funext x y
      exact propext ⟨fun ⟨t,ht,_⟩ => valid ⟨t,ht⟩, False.elim⟩
    rw [he]
    exact PrefixBounds.empty.mono (Nat.zero_le _)

/-- Fixed scheme and fixed coordinate, in the precise named model language.
The two contracts on primitive programs are finite-letter semilinearity and
uniform bounded-prefix behavior. -/
theorem definable_run_fiber (i : I)
    (finiteGraph : ∀ {n} (k : Name n), LiftDefinable Subtype.val (schemeGraph i k))
    (bounded : ∀ {n} (k : Name n), ∃ b, ∀ p, PrefixBounds (schemeGraph i k p) b)
    {n} (k : Name n) (c : Code i) :
    Definable {v : Fin n → VectorGroup I | run i k (Sum.inr ∘ v) = some c} := by
  obtain ⟨m,l,q,hq⟩ := run_covers_vectors i c
  obtain ⟨a,ha⟩ := bounded k
  obtain ⟨b,hb⟩ := bounded l
  have sem := lifted_equality_fiber Subtype.val_injective
    (R := schemeGraph i k) (S := schemeGraph i l) (Definable.exists_head (vectorAffineSamples i))
    (finiteGraph k) (finiteGraph l) q a b ha (hb q)
  convert sem using 1
  ext p
  change (run i k (Sum.inr ∘ p) = some c) ↔ _
  rw [run_vectors_iff]
  have right := (run_vectors_iff i l q c).mp hq
  change (∀ x y, schemeGraph i k p x y ↔ c.val x = y) ↔
    ∀ x y, schemeGraph i k p x y ↔ schemeGraph i l q x y
  exact ⟨fun f x y => (f x y).trans (right x y).symm, fun f x y => (f x y).trans (right x y)⟩

end KnightModel.RankTwo.Concrete
