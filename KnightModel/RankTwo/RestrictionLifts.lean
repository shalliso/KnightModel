import KnightModel.RankTwo.RankModel
import KnightModel.RankTwo.ScottCountable

/-! # Working with finite lifts of tuples in an arbitrary Scott model

A back-and-forth system can be closed under reindexing by taking all finite
restrictions, permutations and repetitions of its matched tuples. Composing
this system through the target produces a back-and-forth on the source.
-/

namespace KnightModel.RankTwo.Scott

namespace BackAndForth

universe u v w
variable {R : ℕ → Type u} {M : Type v} {N : Type w} {D : Model R M} {E : Model R N}
variable (F : BackAndForth D E)

/-- A finite selection of coordinates of one tuple matched by the system. -/
def Lifts {n : ℕ} (s : Tuple M n) (t : Tuple N n) : Prop :=
  ∃ (k : ℕ) (a : Tuple M k) (b : Tuple N k) (p : Fin n → Fin k),
    F.matchTuples a b ∧ s = a ∘ p ∧ t = b ∘ p

theorem Lifts.select {n : ℕ} {s : Tuple M n} {t : Tuple N n} (h : F.Lifts s t)
    {k : ℕ} (q : Fin k → Fin n) : F.Lifts (s ∘ q) (t ∘ q) := by
  obtain ⟨l, a, b, p, hp, rfl, rfl⟩ := h
  exact ⟨l, a, b, p ∘ q, hp, rfl, rfl⟩

private theorem push_select {n k : ℕ} (p : Fin n → Fin k) (x : M) (a : Tuple M k) :
    push x (a ∘ p) = (push x a) ∘ Fin.cases 0 (fun i => (p i).succ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Taking all finite selections preserves the two extension properties. -/
def closure : BackAndForth D E where
  matchTuples := F.Lifts
  atoms := by
    rintro n _ _ ⟨k, a, b, p, hab, rfl, rfl⟩ atom
    cases atom with
    | eq i j => exact F.atoms hab (.eq (p i) (p j))
    | rel r vars => exact F.atoms hab (.rel r (p ∘ vars))
  forth := by
    rintro n _ _ ⟨k, a, b, p, hab, rfl, rfl⟩ x
    obtain ⟨y, hy⟩ := F.forth hab x
    exact ⟨y, k+1, push x a, push y b, _, hy, push_select p x a, push_select p y b⟩
  back := by
    rintro n _ _ ⟨k, a, b, p, hab, rfl, rfl⟩ y
    obtain ⟨x, hx⟩ := F.back hab y
    exact ⟨x, k+1, push x a, push y b, _, hx, push_select p x a, push_select p y b⟩

theorem lifts_of_match {n : ℕ} {s : Tuple M n} {t : Tuple N n} (h : F.matchTuples s t) :
    F.Lifts s t := ⟨n, s, t, id, h, rfl, rfl⟩

/-- Composition of two lifted tuple alignments through the large model. -/
def through : BackAndForth D D where
  matchTuples := fun s u => ∃ t, F.Lifts s t ∧ F.Lifts u t
  atoms := by
    rintro n s u ⟨t, hs, hu⟩ a
    exact (F.closure.atoms hs a).trans (F.closure.atoms hu a).symm
  forth := by
    rintro n s u ⟨t, hs, hu⟩ x
    obtain ⟨y, hy⟩ := F.closure.forth hs x
    obtain ⟨z, hz⟩ := F.closure.back hu y
    exact ⟨z, _, hy, hz⟩
  back := by
    rintro n s u ⟨t, hs, hu⟩ z
    obtain ⟨y, hy⟩ := F.closure.forth hu z
    obtain ⟨x, hx⟩ := F.closure.back hs y
    exact ⟨x, _, hx, hy⟩

theorem Lifts.tail {n : ℕ} {s : Tuple M n} {t : Tuple N n} {x : M} {y : N}
    (h : F.Lifts (push x s) (push y t)) : F.Lifts s t :=
  h.select F Fin.succ

theorem Lifts.eraseSecond {n : ℕ} {s : Tuple M n} {t : Tuple N n} {x z : M} {y w : N}
    (h : F.Lifts (push x (push z s)) (push y (push w t))) : F.Lifts (push x s) (push y t) := by
  have h' := h.select F (Fin.cases (0 : Fin (n+2)) (fun i : Fin n => i.succ.succ))
  convert h' using 1 <;> funext i <;> exact Fin.cases rfl (fun _ => rfl) i

theorem Lifts.exchange {n : ℕ} {s : Tuple M n} {t : Tuple N n} {x z : M} {y w : N}
    (h : F.Lifts (push x (push z s)) (push y (push w t))) :
    F.Lifts (push z (push x s)) (push w (push y t)) := by
  let perm : Fin (n+2) → Fin (n+2) := Fin.cases (1 : Fin (n+2))
    (Fin.cases (0 : Fin (n+2)) (fun i : Fin n => i.succ.succ))
  have h' := h.select F perm
  convert h' using 1 <;> funext i <;> exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

theorem Lifts.head_eq {n : ℕ} {s : Tuple M n} {t : Tuple N n} {x z : M} {y w : N}
    (h : F.Lifts (push x (push z s)) (push y (push w t))) : x = z ↔ y = w :=
  F.closure.atoms h (.eq 0 (0 : Fin (n+1)).succ)

/-- Two source realizations of the same pointed target tuple are conjugate
over all coordinates of their common base. -/
theorem conjugate_of_lifts (C : Presentation R M) {n : ℕ} {s : Tuple M n} {t : Tuple N n}
    {x z : M} {y : N} (h : F.Lifts (push x s) (push y t))
    (h' : F.Lifts (push z s) (push y t)) :
    Conjugate ↥(automorphismGroup D) (List.ofFn s) x z := by
  have hh : F.through.matchTuples (push x s) (push z s) := ⟨_, h, h'⟩
  let e := F.through.pointedIsoOfEnumerations hh C.enum C.onto C.enum C.onto
  let g := (automorphismEquivRelIso D).symm e.val
  refine ⟨g, ?_, e.property 0⟩
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact e.property i.succ

end BackAndForth

theorem ofFn_push {M : Type*} {n : ℕ} (x : M) (s : Tuple M n) :
    List.ofFn (push x s) = x :: List.ofFn s := by
  rw [List.ofFn_succ]
  rfl

end KnightModel.RankTwo.Scott
