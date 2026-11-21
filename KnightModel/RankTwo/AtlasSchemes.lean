import KnightModel.RankTwo.AtlasPieces
import KnightModel.RankTwo.WordSchemes

/-! # Reifying the actual atlas transitions in the countable coordinate language -/

namespace KnightModel.RankTwo

open Set

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

theorem TailShape.schematic (s : TailShape A) :
    Word.Schematic shift o d hd upper (fun x y => s.apply shift x = y) := by
  apply ((Word.schematic_through shift o d hd upper s.endWord).seq
    (Word.schematic_prefix shift o d hd upper s.prefix)).congr
  intro x y
  simp [TailShape.apply]

theorem CoordinateRule.schematic (r : CoordinateRule A) :
    Word.Schematic shift o d hd upper (r.Rel shift o d hd upper) := by
  cases r with
  | first u v =>
    apply ((Word.schematic_through shift o d hd upper u).inv.seq
      (Word.schematic_through shift o d hd upper v)).congr
    intro x y
    exact exists_congr (fun _ => and_congr eq_comm eq_comm)
  | interval l u l' u' =>
    apply ((Word.schematic_H shift o d hd upper l u).inv.seq
      (Word.schematic_H shift o d hd upper l' u')).congr
    intro x y
    constructor
    · rintro ⟨w,⟨h,z,rfl,hz⟩,⟨k,t,ht,hy⟩⟩
      obtain rfl : z = t := Subtype.ext ht
      exact ⟨h,k,z,hz,hy⟩
    · rintro ⟨h,k,z,hx,hy⟩
      exact ⟨z.val,⟨h,z,rfl,hx⟩,⟨k,z,rfl,hy⟩⟩
  | tail s t =>
    apply ((s.schematic shift o d hd upper).inv.seq (t.schematic shift o d hd upper)).congr
    intro x y
    exact exists_congr (fun _ => and_congr eq_comm eq_comm)

theorem GuardedRule.schematic_contains (r : GuardedRule A) :
    Word.Schematic shift o d hd upper (fun x y => r.contains x ∧ x = y) := by
  obtain ⟨lo,hi,r⟩ := r
  cases lo with
  | none =>
    apply (Word.schematic_atMost shift o d hd upper hi).congr
    intro x y
    simp [GuardedRule.contains]
  | some lo =>
    apply ((Word.schematic_above shift o d hd upper lo).seq
      (Word.schematic_atMost shift o d hd upper hi)).congr
    intro x y
    simp [GuardedRule.contains, and_assoc]

theorem GuardedRule.schematic (r : GuardedRule A) :
    Word.Schematic shift o d hd upper
      (fun x y => r.contains x ∧ r.rule.Rel shift o d hd upper x y) := by
  apply ((r.schematic_contains shift o d hd upper).seq (r.rule.schematic shift o d hd upper)).congr
  intro x y
  simp

theorem GuardedRule.schematic_list (rs : List (GuardedRule A)) :
    Word.Schematic shift o d hd upper
      (fun x y => ∃ r ∈ rs, r.contains x ∧ r.rule.Rel shift o d hd upper x y) := by
  induction rs with
  | nil => simpa using Word.schematic_empty shift o d hd upper
  | cons r rs ih =>
    apply ((r.schematic shift o d hd upper).union ih).congr
    intro x y
    simp

variable {J : Type*} [LinearOrder J] [WellFoundedLT J] (C : CoherentLadders J A)

/-- Every geometrically realized change in this atlas belongs to the same
countable scheme language used for the countable frame structure. -/
theorem CoherentLadders.schematic_change {b c : J} (hbc : b ≤ c) :
    Word.Schematic shift o d hd upper (fun x y =>
      C.markedRows.change (C.transports shift o d hd upper) hbc x = y) := by
  obtain ⟨rs,hr⟩ := C.change_graph shift o d hd upper hbc
  exact (GuardedRule.schematic_list shift o d hd upper rs).congr (fun x y => (hr x y).symm)

end KnightModel.RankTwo
