import KnightModel.RankTwo.UnaryChoice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image

/-! # Finite tests for unary linear inequalities -/

namespace KnightModel.RankTwo.UnaryChoice

open Set

variable {V : Type*} [LinearOrder V]

/-- Same open interval, or the same endpoint, in the cut by finitely many thresholds. -/
def SameCell (E : List V) (x y : V) : Prop :=
  ∀ a ∈ E, (x < a ↔ y < a) ∧ (a < x ↔ a < y)

theorem SameCell.symm {E : List V} {x y : V} (h : SameCell E x y) : SameCell E y x :=
  fun a ha => ⟨(h a ha).1.symm, (h a ha).2.symm⟩

/-- A finite list of candidate witnesses. The same list construction can be
used on affine expressions before evaluating their free variables. -/
def samples (P : Samples V) (E : List V) : List V :=
  [P.base] ++ E ++ E.map P.down ++ E.map P.up ++ E.flatMap (fun a => E.map (P.mid a))

/-- Every sign pattern at a point is attained by one of the sampled points. -/
theorem exists_sample (P : Samples V) (E : List V) (x : V) :
    ∃ y ∈ samples P E, SameCell E x y := by
  classical
  by_cases hx : x ∈ E
  · exact ⟨x, by simp [samples, hx], fun _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  let L := E.toFinset.filter (· < x)
  let U := E.toFinset.filter (x < ·)
  have good (y : V) (hl : ∀ l ∈ L, l < y) (hu : ∀ u ∈ U, y < u) : SameCell E x y := by
    intro a ha
    rcases lt_trichotomy a x with h | rfl | h
    · have h' := hl a (by simp [L, ha, h])
      exact ⟨iff_of_false (not_lt_of_gt h) (not_lt_of_gt h'), iff_of_true h h'⟩
    · exact (hx ha).elim
    · have h' := hu a (by simp [U, ha, h])
      exact ⟨iff_of_true h h', iff_of_false (not_lt_of_gt h) (not_lt_of_gt h')⟩
  by_cases hL : L.Nonempty
  · let l := L.max' hL
    have hl : l ∈ E ∧ l < x := by simpa only [L, Finset.mem_filter, List.mem_toFinset] using (show l ∈ L from L.max'_mem hL)
    by_cases hU : U.Nonempty
    · let u := U.min' hU
      have hu : u ∈ E ∧ x < u := by simpa only [U, Finset.mem_filter, List.mem_toFinset] using (show u ∈ U from U.min'_mem hU)
      obtain ⟨hm, hm'⟩ := P.between l u (hl.2.trans hu.2)
      refine ⟨P.mid l u, ?_, good _ (fun _ h => (L.le_max' _ h).trans_lt hm)
        (fun _ h => hm'.trans_le (U.min'_le _ h))⟩
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨l, hl.1, List.mem_map.mpr ⟨u, hu.1, rfl⟩⟩
    · refine ⟨P.up l, ?_, good _ (fun _ h => (L.le_max' _ h).trans_lt (P.lt_up _))
        (fun u h => (hU ⟨u,h⟩).elim)⟩
      simp [samples, List.mem_map.mpr ⟨l, hl.1, rfl⟩]
  · by_cases hU : U.Nonempty
    · let u := U.min' hU
      have hu : u ∈ E ∧ x < u := by simpa only [U, Finset.mem_filter, List.mem_toFinset] using (show u ∈ U from U.min'_mem hU)
      refine ⟨P.down u, ?_, good _ (fun l h => (hL ⟨l,h⟩).elim)
        (fun _ h => (P.down_lt _).trans_le (U.min'_le _ h))⟩
      simp [samples, List.mem_map.mpr ⟨u, hu.1, rfl⟩]
    · exact ⟨P.base, by simp [samples], good _ (fun l h => (hL ⟨l,h⟩).elim)
        (fun u h => (hU ⟨u,h⟩).elim)⟩

private noncomputable def signCell (E : List V) (z : V) : Cell V := by
  classical
  let L := E.toFinset.filter (· < z)
  let bound := if z ∈ E then some z else if hn : L.Nonempty then some (L.max' hn) else none
  refine ⟨{x | SameCell E z x}, bound, ?_, ?_⟩
  · intro a ha x hx
    change SameCell E z x at hx
    by_cases hz : z ∈ E
    · have he : z = a := by simpa [bound, hz] using ha
      exact he ▸ le_of_not_gt (fun h => (lt_irrefl z) ((hx z hz).1.mpr h))
    · by_cases hn : L.Nonempty
      · have he : L.max' hn = a := by simpa [bound, hz, hn] using ha
        have hm : a ∈ L := he ▸ L.max'_mem hn
        obtain ⟨haE, haz⟩ : a ∈ E ∧ a < z := by simpa only [L, Finset.mem_filter, List.mem_toFinset] using hm
        exact ((hx a haE).2.mp haz).le
      · simp [bound, hz, hn] at ha
  · intro x hx y hy lower
    change SameCell E z x at hx
    change SameCell E z y
    intro a ha
    rcases lt_trichotomy a z with haz | he | hza
    · have hay : a < y := by
        by_cases hz : z ∈ E
        · exact haz.trans (lower z (by simp [bound, hz]))
        · have hm : a ∈ L := by simp [L, ha, haz]
          have hne : L.Nonempty := ⟨a, hm⟩
          exact (L.le_max' _ hm).trans_lt (lower (L.max' hne) (by
            simp [bound, hz, hne]))
      exact ⟨iff_of_false (not_lt_of_gt haz) (not_lt_of_gt hay), iff_of_true haz hay⟩
    · subst a
      have hzx : ¬z < x := fun h => (lt_irrefl z) ((hx z ha).2.mpr h)
      exact (hzx ((lower z (by simp [bound, ha])).trans hy)).elim
    · have hya := hy.trans ((hx a ha).1.mp hza)
      exact ⟨iff_of_true hza hya, iff_of_false (not_lt_of_gt hza) (not_lt_of_gt hya)⟩

/-- A unary predicate determined by comparisons with finitely many points
has a finite monochromatic interval decomposition. -/
theorem decomposed_of_thresholds (P : Samples V) (E : List V) (S : Set V)
    (h : ∀ x y, SameCell E x y → (x ∈ S ↔ y ∈ S)) : Decomposed S := by
  classical
  refine ⟨(samples P E).map (signCell E), ?_, ?_⟩
  · intro x
    obtain ⟨z, hz, hcell⟩ := exists_sample P E x
    exact ⟨signCell E z, List.mem_map.mpr ⟨z, hz, rfl⟩, hcell.symm⟩
  · rintro c hc
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hc
    by_cases hz : z ∈ S
    · exact .inl fun x hx => (h z x hx).mp hz
    · exact .inr fun x hx hxs => hz ((h z x hx).mpr hxs)

end KnightModel.RankTwo.UnaryChoice
