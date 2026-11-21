import KnightModel.RankTwo.Words
import KnightModel.RankTwo.PrefixProgram

/-!
# Bounded inspection for the folds and their inverses

The algorithms use a single-letter tail translation at each step and copy the
rest of the input. In particular the inverse is a partial map on words, rejecting
precisely those outside the chart.
-/

namespace KnightModel.RankTwo.Word

variable {A : Type*} [LinearOrder A]

/-- Undo the change to the first letter in the compressed cone. -/
def unshift (a : A) (shift : Set.Ici a ≃o A) : Word A → Word A
  | [] => root
  | t :: w => cons (shift.symm t).1 w

/-- Decode one fold, inspecting the first letter to decide whether the inner
chart must be decoded. -/
def unfoldStep (a : A) (shift : Set.Ici a ≃o A) (g : Word A → Option (Word A)) :
    Word A → Option (Word A)
  | [] => none
  | t :: w =>
    if t < a then some (cons t w) else
      if t = a then (g w).map (unshift a shift) else none

/-- Partial inverse of the chart through a word. -/
def unthrough (shift : ∀ a : A, Set.Ici a ≃o A) : Word A → Word A → Option (Word A)
  | [] => some
  | a :: u => unfoldStep a (shift a) (unthrough shift u)

private theorem unfoldStep_foldStep (a : A) (s : Set.Ici a ≃o A)
    {f : Word A → Word A} {g : Word A → Option (Word A)}
    (hg : ∀ w, g (f w) = some w) (w : Word A) :
    unfoldStep a s g (foldStep a s f w) = some w := by
  cases w with
  | nil =>
    change (if a < a then _ else if a = a then (g (f root)).map _ else _) = _
    simp [hg, root, unshift]
  | cons t w =>
    by_cases h : t < a
    · simp [foldStep, h, cons, unfoldStep]
    · change unfoldStep a s g (if h : t < a then _ else _) = _
      rw [dif_neg h]
      change (if a < a then _ else if a = a then
        (g (f (cons (s ⟨t, le_of_not_gt h⟩) w))).map _ else _) = _
      simp [hg, cons, unshift]

@[simp] theorem unthrough_through (shift : ∀ a : A, Set.Ici a ≃o A) (u w : Word A) :
    unthrough shift u (through shift u w) = some w := by
  induction u generalizing w with
  | nil => rfl
  | cons a u ih => exact unfoldStep_foldStep a (shift a) ih w

private theorem foldStep_eq_of_decode (a : A) (s : Set.Ici a ≃o A)
    {f : Word A → Word A} {g : Word A → Option (Word A)}
    (hg : ∀ w x, g w = some x → f x = w) (z x : Word A)
    (h : unfoldStep a s g z = some x) : foldStep a s f x = z := by
  cases z with
  | nil => contradiction
  | cons t w =>
    by_cases ht : t < a
    · have hx : cons t w = x := by simpa [unfoldStep, ht] using h
      subst x
      simp [cons, foldStep, ht]
    · by_cases heq : t = a
      · subst t
        change (if a < a then _ else if a = a then (g w).map _ else _) = some x at h
        simp only [lt_irrefl, ↓reduceIte] at h
        cases hgw : g w with
        | none => simp [hgw] at h
        | some y =>
          simp only [hgw, Option.map_some, Option.some.injEq] at h
          subst x
          have hy := hg w y hgw
          cases y with
          | nil => exact congrArg (cons a) hy
          | cons r y =>
            let t := s.symm r
            change (if h : t.1 < a then _ else _) = _
            rw [dif_neg (not_lt_of_ge t.2)]
            change cons a (f (cons (s t) y)) = cons a w
            simpa [t, cons] using congrArg (cons a) hy
      · simp [unfoldStep, ht, heq] at h

theorem unthrough_eq_some_iff (shift : ∀ a : A, Set.Ici a ≃o A) (u z x : Word A) :
    unthrough shift u z = some x ↔ through shift u x = z := by
  constructor
  · induction u generalizing z x with
    | nil => exact fun h => (Option.some.inj h).symm
    | cons a u ih => exact foldStep_eq_of_decode a (shift a) ih z x
  · rintro rfl
    exact unthrough_through shift u x

private theorem foldStep_inspects (a : A) (s : Set.Ici a ≃o A) (n : Nat)
    (f : Word A → Word A) (hf : InspectsAtMost n (fun w : List A => some (f w))) :
    InspectsAtMost (n+1) (fun w : List A => some (foldStep a s f w)) := by
  intro p suffix hp
  cases p with
  | nil => simp at hp
  | cons t p =>
    by_cases ht : t < a
    · simp [foldStep, cons, ht]
    · have hlen : n ≤ (s ⟨t, le_of_not_gt ht⟩ :: p).length := by
        simp only [List.length_cons] at hp ⊢
        omega
      have aux := hf (s ⟨t, le_of_not_gt ht⟩ :: p) suffix hlen
      simp only [Option.map_some, Option.some.injEq, List.cons_append] at aux
      simp only [List.cons_append, foldStep, dif_neg ht, Option.map_some, Option.some.injEq]
      exact congrArg (cons a) aux

/-- A chart through a word reads at most its length before it copies the suffix. -/
theorem through_inspects (shift : ∀ a : A, Set.Ici a ≃o A) (u : Word A) :
    InspectsAtMost (List.length (α := A) u) (fun w : List A => some (through shift u w)) := by
  induction u with
  | nil => intro _ _ _; rfl
  | cons a u ih => exact foldStep_inspects a (shift a) _ _ ih

private theorem unshift_inspects (a : A) (s : Set.Ici a ≃o A) :
    InspectsAtMost 1 (fun w : List A => some (unshift a s w)) := by
  intro p suffix hp
  cases p with
  | nil => simp at hp
  | cons t p => rfl

private theorem unfoldStep_inspects (a : A) (s : Set.Ici a ≃o A) (n : Nat)
    (g : Word A → Option (Word A)) (hg : InspectsAtMost n g) :
    InspectsAtMost (n+2) (unfoldStep a s g) := by
  have hu := hg.bind (unshift_inspects a s)
  have eqfun : (fun w : List A => (g w).bind fun z => some (unshift a s z)) =
      (fun w : List A => (g w).map (unshift a s)) := by
    funext w
    cases g w <;> rfl
  have hu' := Eq.mp (congrArg (fun f : List A → Option (List A) => InspectsAtMost (n+1) f) eqfun) hu
  intro p suffix hp
  cases p with
  | nil => simp at hp
  | cons t p =>
    have hlen : n + 1 ≤ p.length := by
      simp only [List.length_cons] at hp
      omega
    by_cases ht : t < a
    · simp only [List.cons_append, unfoldStep, if_pos ht]
      rfl
    · by_cases heq : t = a
      · subst t
        simp only [List.cons_append, unfoldStep, lt_irrefl, if_false, if_true]
        exact hu' p suffix hlen
      · simp only [List.cons_append, unfoldStep, if_neg ht, if_neg heq]
        rfl

/-- The partial inverse reads at most two further letters per folded cone. -/
theorem unthrough_inspects (shift : ∀ a : A, Set.Ici a ≃o A) (u : Word A) :
    InspectsAtMost (2 * List.length (α := A) u) (unthrough shift u) := by
  induction u with
  | nil => intro _ _ _; rfl
  | cons a u ih =>
    rw [List.length_cons, Nat.mul_add, Nat.mul_one]
    exact unfoldStep_inspects a (shift a) _ _ ih

end KnightModel.RankTwo.Word
