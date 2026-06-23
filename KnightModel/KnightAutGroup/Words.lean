/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.PartialIso
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Words for the Knight Group Construction

This file defines the basic word combinatorics used to describe elements of the free group
acting on `ℚ`, and sets up the algebraic infrastructure needed to reason about the evaluation
of words via `evalWord`.

## Main definitions

* `Letter` = `ℕ × Bool`: a generator index and a direction (`false` = forward, `true` = inverse).
* `Word` = `List Letter`: a sequence of letters representing a free group element.
* `letterInv`, `wordInv`: formal inverses at the letter and word level.
* `wordEquiv w₁ w₂`: equality in the free group `FreeGroup ℕ`.
* `Word.isReduced`: the standard predicate — no adjacent `l, l⁻¹` pair.

## Main results

* `wordEquiv_iff_wordInv_append`: `w₁ ≡ w₂` iff `w₂⁻¹ ++ w₁ ≡ []`.
* `Word.isReduced_tail`, `Word.isReduced_map_letterInv`: closure of `isReduced` under tails
  and letter-wise inversion.

## Tags

knight group, free group, word, letter, reduced word
-/

/-! ## Letters and Words -/

/-- A `Letter` encodes a generator: `n` is the generator index, `false` = forward application,
    `true` = inverse application. -/
abbrev Letter := ℕ × Bool

/-- A `Word` is a list of `Letter`s, representing an element of the free group on `ℕ`. -/
abbrev Word := List Letter

/-- The formal inverse of a letter: flip the direction bit. -/
def letterInv : Letter → Letter
  | (n, b) => (n, !b)

/-- The formal inverse of a word: reverse the list and invert each letter. -/
def wordInv (w : Word) : Word :=
  (w.map letterInv).reverse

instance : InvolutiveInv Letter where
  inv := letterInv
  inv_inv l := by obtain ⟨n, b⟩ := l; simp [letterInv]

instance : InvolutiveInv Word where
  inv := wordInv
  inv_inv w := by
    simp only [wordInv, List.map_reverse, List.map_map, List.reverse_reverse, Function.comp_def]
    simp [letterInv]

@[simp] lemma letter_inv_def (n : ℕ) (b : Bool) : ((n, b) : Letter)⁻¹ = (n, !b) := rfl

/-- Two words are `wordEquiv` if they represent the same element in `FreeGroup ℕ`. -/
def wordEquiv (w₁ w₂ : Word) : Prop :=
  FreeGroup.mk w₁ = FreeGroup.mk w₂

lemma wordInv_eq_invRev (w : Word) : w⁻¹ = FreeGroup.invRev w := by
  change wordInv w = FreeGroup.invRev w
  simp only [wordInv, FreeGroup.invRev]; congr 1

lemma wordEquiv_iff_wordInv_append (w₁ w₂ : Word) :
    wordEquiv w₁ w₂ ↔ wordEquiv (w₂⁻¹ ++ w₁) [] := by
  have hmk : (FreeGroup.mk ([] : Word) : FreeGroup ℕ) = 1 := rfl
  simp only [wordEquiv, wordInv_eq_invRev, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
    hmk, inv_mul_eq_one, eq_comm]

lemma wordEquiv_iff_append_wordInv (w₁ w₂ : Word) :
    wordEquiv w₁ w₂ ↔ wordEquiv (w₁ ++ w₂⁻¹) [] := by
  have hmk : (FreeGroup.mk ([] : Word) : FreeGroup ℕ) = 1 := rfl
  simp only [wordEquiv, wordInv_eq_invRev, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
    hmk, mul_inv_eq_one]

/-- A word is *reduced* if no two adjacent letters are inverses of each other.
    Reduced words are canonical representatives in the free group. -/
def Word.isReduced : Word → Prop
  | [] => True
  | [_] => True
  | l₁ :: l₂ :: w => l₁⁻¹ ≠ l₂ ∧ Word.isReduced (l₂ :: w)

lemma Word.isReduced_tail {l : Letter} {w : Word} (h : Word.isReduced (l :: w)) :
    Word.isReduced w := by
  cases w with
  | nil => trivial
  | cons l' w' => exact h.2

lemma Word.isReduced_map_letterInv {w : Word} (h : Word.isReduced w) :
    Word.isReduced (w.map (fun l : Letter => l⁻¹)) := by
  induction w with
  | nil => trivial
  | cons l₁ w ih =>
    cases w with
    | nil => trivial
    | cons l₂ w =>
      simp only [List.map_cons, Word.isReduced] at h ⊢
      refine ⟨fun heq => h.1 ?_, ih h.2⟩
      rw [inv_inv] at heq
      rw [heq, inv_inv]
