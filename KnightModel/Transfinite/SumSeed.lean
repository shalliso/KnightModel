import KnightModel.Transfinite.SumScott
import KnightModel.Transfinite.SumBound
import KnightModel.Transfinite.SumOrder

/-! # The seed and its realizations at countable limit stages -/

namespace KnightModel.Transfinite
open RankTwo.Scott Cardinal NamedSum

private theorem mark_block {X : ℕ → Type} {R : ℕ → ℕ → Type} (D : ∀ i, Model (R i) (X i))
    (r : R 0 1) (x : X 0) (hm : ∀ t, D 0 r t ↔ t 0 = x) (v : Tuple (Carrier X) 1) :
    Block D 0 r v ↔ v 0 = inject 0 x := by
  constructor
  · rintro ⟨w,eq,h⟩
    exact (eq 0).trans (congrArg _ ((hm w).mp h))
  · intro h
    exact ⟨fun _ => x,fun l => by simpa only [Subsingleton.elim l 0] using h,(hm _).mpr rfl⟩

noncomputable def sumSeed (P : ℕ → Seed) : Seed where
  R := Relation (fun i => (P i).R)
  M := Carrier (fun i => (P i).M)
  D := model (fun i => (P i).D) (fun i => (P i).leSym)
  countRel := fun _ => inferInstance
  countM := inferInstanceAs (Countable (Σ i, (P i).M))
  ord := inferInstance
  mark := inject 0 (P 0).mark
  leSym := .order
  le_iff := order_iff _ _ (fun i => (P i).le_iff)
  markSym := .block 0 (P 0).markSym
  mark_iff := mark_block (D := fun i => (P i).D) (P 0).markSym (P 0).mark (P 0).mark_iff

theorem sumSeed_bounded (P : ℕ → Seed) (κ : Cardinal) (inf : ℵ₀ ≤ κ)
    (hb : ∀ i, (P i).Bounded κ) : (sumSeed P).Bounded κ := by
  intro N E h
  obtain ⟨F,empty⟩ := ((sumSeed P).pres.satisfies_iff_backAndForth _ _).mp h
  apply bound (D := fun i => (P i).D) (leSym := fun i => (P i).leSym) F empty inf
  intro i
  apply hb i (fiberModel E i)
  exact ((P i).pres.satisfies_iff_backAndForth _ _).mpr ⟨project F i,project_empty F empty i⟩

noncomputable def sumSeed_realizes (P : ℕ → Seed) (k : ℕ → Cardinal) (κ : Cardinal)
    (inf : ℵ₀ ≤ κ) (le : ∀ i, k i ≤ κ) (sup : ∀ c, (∀ i, k i ≤ c) → κ ≤ c)
    (A : ∀ i, (P i).Realizes (k i)) : (sumSeed P).Realizes κ := by
  let F (i : ℕ) := (P i).pres.system (P i).D (A i).E (A i).sat
  have empty (i : ℕ) : (F i).matchTuples (n := 0) Fin.elim0 Fin.elim0 :=
    (((P i).pres.sentence_iff (P i).D (A i).E).mp (A i).sat).1
  let seq := longSequence k κ sup (fun i => (A i).seq)
  refine {
    N := Carrier (fun i => (A i).N), E := model (fun i => (A i).E) (fun i => (P i).leSym)
    ord := inferInstance, mark := inject 0 (A 0).mark
    le_iff := order_iff _ _ (fun i => (A i).le_iff)
    mark_iff := mark_block (D := fun i => (A i).E) (P 0).markSym (A 0).mark (A 0).mark_iff
    sat := ((sumSeed P).pres.satisfies_iff_backAndForth _ _).mpr
      ⟨system F (fun i => (P i).leSym), system_empty F _ empty⟩
    seq := seq, size := le_antisymm ?_ ?_ }
  · exact sum_size_le (fun i => (A i).N) inf (fun i => (A i).size.le.trans (le i))
  · simpa only [Cardinal.mk_toType,Cardinal.card_ord] using
      Cardinal.mk_le_of_injective seq.injective

end KnightModel.Transfinite
