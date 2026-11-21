import Std

/-!
# Finite inspection of word coordinates

A program reads letters from the front, branches on tests of its registers,
and either rejects or replaces the inspected part by an output string.
Tests and outputs are interpreted separately. For the vector alphabet these
can be given by formulas and tuples of terms of the ordered vector group.
-/

namespace KnightModel.RankTwo

/-- A partial map that always copies the suffix beyond the first `n` letters. -/
def InspectsAtMost {A : Type u} (n : Nat) (f : List A → Option (List A)) : Prop :=
  ∀ p s : List A, n ≤ p.length → f (p ++ s) = (f p).map (· ++ s)

namespace InspectsAtMost

theorem mono {A : Type u} {m n : Nat} {f : List A → Option (List A)}
    (h : InspectsAtMost m f) (hmn : m ≤ n) : InspectsAtMost n f :=
  fun p s hn => h p s (Nat.le_trans hmn hn)

/-- Equality, including equality of rejection domains, can be checked on words
of length at most the common inspection bound. -/
theorem ext_iff {A : Type u} {n : Nat} {f g : List A → Option (List A)}
    (hf : InspectsAtMost n f) (hg : InspectsAtMost n g) :
    f = g ↔ ∀ p : List A, p.length ≤ n → f p = g p := by
  constructor
  · rintro rfl p _; rfl
  · intro he
    funext w
    by_cases hw : w.length ≤ n
    · exact he w hw
    · have hn : n ≤ (w.take n).length := by simp; omega
      have hle : (w.take n).length ≤ n := by simp; omega
      calc f w = f (w.take n ++ w.drop n) := by rw [List.take_append_drop]
           _ = (f (w.take n)).map (· ++ w.drop n) := hf _ _ hn
           _ = (g (w.take n)).map (· ++ w.drop n) := by rw [he _ hle]
           _ = g (w.take n ++ w.drop n) := (hg _ _ hn).symm
           _ = g w := by rw [List.take_append_drop]

/-- The sum of the two bounds suffices, even if the first map erases all of
its inspected letters. -/
theorem bind {A : Type u} {m n : Nat} {f g : List A → Option (List A)}
    (hf : InspectsAtMost m f) (hg : InspectsAtMost n g) :
    InspectsAtMost (m+n) (fun w => (f w).bind g) := by
  intro p s hp
  let x := p.take m
  let y := p.drop m
  have split : x ++ y = p := List.take_append_drop _ _
  have hx : m ≤ x.length := by simp [x]; omega
  have hy : n ≤ y.length := by simp [y]; omega
  change (f (p ++ s)).bind g = ((f p).bind g).map (· ++ s)
  rw [← split, List.append_assoc, hf x _ hx, hf x _ hx]
  cases h : f x with
  | none => rfl
  | some z =>
    change g (z ++ (y ++ s)) = (g (z ++ y)).map (· ++ s)
    rw [← List.append_assoc]
    exact hg _ _ (by simp; omega)

end InspectsAtMost

/-- Registers are the letters read so far, most recent first. Which tests and
output instructions are available is determined by the instruction alphabets. -/
inductive PrefixProgram (Test Out : Type) where
  | reject
  | emit (instructions : List Out)
  | branch (test : Test) (yes no : PrefixProgram Test Out)
  | read (atEnd next : PrefixProgram Test Out)
  deriving Repr

namespace PrefixProgram

variable {Test Out : Type} {A : Type u}

def depth : PrefixProgram Test Out → Nat
  | .reject | .emit _ => 0
  | .branch _ y n => max y.depth n.depth
  | .read done step => 1 + max done.depth step.depth

/-- An undefined output letter rejects the input. This allows the vector
language to return values outside its nonnegative alphabet. -/
def run (test : Test → List A → Bool) (output : Out → List A → Option A) :
    PrefixProgram Test Out → List A → List A → Option (List A)
  | .reject, _, _ => none
  | .emit os, r, w => (os.mapM (output · r)).map (· ++ w)
  | .branch t y n, r, w => if test t r then y.run test output r w else n.run test output r w
  | .read e _, r, [] => e.run test output r []
  | .read _ c, r, x :: w => c.run test output (x :: r) w

theorem run_inspectsAtMost (test : Test → List A → Bool) (output : Out → List A → Option A)
    (code : PrefixProgram Test Out) (r : List A) :
    InspectsAtMost code.depth (code.run test output r) := by
  induction code generalizing r with
  | reject => intro p s _; rfl
  | emit os =>
    intro p s _
    simp only [run]
    cases os.mapM (output · r) <;> simp [List.append_assoc]
  | branch t y n iy ino =>
    intro p s hp
    change max y.depth n.depth ≤ p.length at hp
    cases h : test t r <;> simp only [run, h, Bool.false_eq_true, ↓reduceIte]
    · exact ino r p s (Nat.le_trans (Nat.le_max_right ..) hp)
    · exact iy r p s (Nat.le_trans (Nat.le_max_left ..) hp)
  | read e c _ ic =>
    intro p s hp
    cases p with
    | nil => simp [depth] at hp
    | cons x p =>
      change 1 + max e.depth c.depth ≤ p.length + 1 at hp
      exact ic (x :: r) p s (by omega)

end PrefixProgram
end KnightModel.RankTwo
