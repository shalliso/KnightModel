/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import KnightModel.RankTwo.ScottSentence

/-! # Uniqueness of the countable model of the Scott sentence -/

namespace KnightModel.RankTwo.Scott

universe u v w

structure RelIso {R : Nat → Type u} {M : Type v} {N : Type w}
    (D : Model R M) (E : Model R N) where
  toFun : M → N
  invFun : N → M
  leftInv : ∀ a, invFun (toFun a) = a
  rightInv : ∀ b, toFun (invFun b) = b
  map_rel : ∀ {k} (r : R k) (t : Tuple M k), D r t ↔ E r (toFun ∘ t)

namespace BackAndForth

variable {R : Nat → Type u} {M : Type v} {N : Type w} {D : Model R M} {E : Model R N}
variable (F : BackAndForth D E)

private structure Stage where
  len : Nat
  s : Tuple M len
  t : Tuple N len
  ok : F.matchTuples s t

variable {F}

private def Stage.Mem (p : F.Stage) (a : M) (b : N) := ∃ i, p.s i = a ∧ p.t i = b

private noncomputable def Stage.next (p : F.Stage) (a : M) (b : N) : F.Stage :=
  let y := (F.forth p.ok a).choose
  let h := (F.forth p.ok a).choose_spec
  let x := (F.back h b).choose
  { len := p.len + 2
    s := push x (push a p.s)
    t := push b (push y p.t)
    ok := (F.back h b).choose_spec }

private theorem Stage.keeps (p : F.Stage) (a : M) (b : N) {x y}
    (m : p.Mem x y) : (p.next a b).Mem x y := by
  obtain ⟨i, hi, hj⟩ := m
  exact ⟨i.succ.succ, hi, hj⟩

private theorem Stage.fst (p : F.Stage) (a : M) (b : N) : ∃ y, (p.next a b).Mem a y :=
  ⟨_, (0 : Fin (p.len+1)).succ, rfl, rfl⟩

private theorem Stage.snd (p : F.Stage) (a : M) (b : N) : ∃ x, (p.next a b).Mem x b :=
  ⟨_, (0 : Fin (p.len + 2)), rfl, rfl⟩

private noncomputable def stages (p : F.Stage) (a : Nat → M) (b : Nat → N) : Nat → F.Stage
  | 0 => p
  | i+1 => (stages p a b i).next (a i) (b i)

private theorem stages_mono (p : F.Stage) (a : Nat → M) (b : Nat → N)
    {i j : Nat} (h : i ≤ j) {x y} (m : (stages p a b i).Mem x y) :
    (stages p a b j).Mem x y := by
  induction h with
  | refl => exact m
  | step h ih => exact Stage.keeps _ _ _ ih

private theorem finite_bound {k : Nat} (f : Fin k → Nat) : ∃ n, ∀ i, f i ≤ n := by
  induction k with
  | zero => exact ⟨0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih (fun i => f i.succ)
    exact ⟨max (f 0) n, Fin.cases (Nat.le_max_left _ _) (fun i =>
      Nat.le_trans (hn i) (Nat.le_max_right _ _))⟩

variable (F)

/-- Alternating enumeration extends any matched finite tuple to an isomorphism. -/
noncomputable def pointedIsoOfEnumerations {n} {s : Tuple M n} {t : Tuple N n} (h : F.matchTuples s t)
    (a : Nat → M) (ha : ∀ x, ∃ i, a i = x)
    (b : Nat → N) (hb : ∀ y, ∃ i, b i = y) : {e : RelIso D E // ∀ i, e.toFun (s i) = t i} := by
  classical
  let p : F.Stage := ⟨n, s, t, h⟩
  let S := stages p a b
  let G (x : M) (y : N) := ∃ i, (S i).Mem x y
  have total (x : M) : ∃ y, G x y := by
    obtain ⟨i, rfl⟩ := ha x
    obtain ⟨y, hy⟩ := (S i).fst (a i) (b i)
    exact ⟨y, i+1, hy⟩
  have onto (y : N) : ∃ x, G x y := by
    obtain ⟨i, rfl⟩ := hb y
    obtain ⟨x, hx⟩ := (S i).snd (a i) (b i)
    exact ⟨x, i+1, hx⟩
  have eq_iff {x x' : M} {y y' : N} (xy : G x y) (xy' : G x' y') :
      x = x' ↔ y = y' := by
    obtain ⟨i, hi⟩ := xy
    obtain ⟨j, hj⟩ := xy'
    let z := max i j
    obtain ⟨k, hk, hk'⟩ := stages_mono p a b (j := z) (Nat.le_max_left _ _) hi
    obtain ⟨l, hl, hl'⟩ := stages_mono p a b (j := z) (Nat.le_max_right _ _) hj
    have e := F.atoms (S z).ok (.eq k l)
    change (S z).s k = (S z).s l ↔ (S z).t k = (S z).t l at e
    exact hk ▸ hl ▸ hk' ▸ hl' ▸ e
  let f := fun x => (total x).choose
  let g := fun y => (onto y).choose
  refine ⟨{ toFun := f, invFun := g
            leftInv := fun x => (eq_iff (onto (f x)).choose_spec (total x).choose_spec).mpr rfl
            rightInv := fun y => (eq_iff (total (g y)).choose_spec (onto y).choose_spec).mp rfl
            map_rel := ?_ }, fun i => (eq_iff (total (s i)).choose_spec
             (show G (s i) (t i) from ⟨0, i, rfl, rfl⟩)).mp rfl⟩
  intro k r t
  let idx (i : Fin k) := (total (t i)).choose_spec.choose
  obtain ⟨j, hj⟩ := finite_bound idx
  have mem (i : Fin k) : (S j).Mem (t i) (f (t i)) :=
    stages_mono p a b (hj i) (total (t i)).choose_spec.choose_spec
  let vars := fun i => (mem i).choose
  have hs : (S j).s ∘ vars = t := funext fun i => (mem i).choose_spec.1
  have ht : (S j).t ∘ vars = f ∘ t := funext fun i => (mem i).choose_spec.2
  have e := F.atoms (S j).ok (.rel r vars)
  change D r ((S j).s ∘ vars) ↔ E r ((S j).t ∘ vars) at e
  simpa only [hs, ht] using e

/-- Alternating enumeration of the two carriers produces a genuine isomorphism. -/
noncomputable def isoOfEnumerations (h : F.matchTuples (n := 0) Fin.elim0 Fin.elim0)
    (a : Nat → M) (ha : ∀ x, ∃ i, a i = x)
    (b : Nat → N) (hb : ∀ y, ∃ i, b i = y) : RelIso D E :=
  (F.pointedIsoOfEnumerations h a ha b hb).val

end BackAndForth

namespace Presentation

/-- Every countable, nonempty model of the Scott sentence is isomorphic to its source. -/
noncomputable def isoOfSatisfies {R : Nat → Type u} {M : Type v} {N : Type w}
    (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D)) (b : Nat → N) (hb : ∀ y, ∃ i, b i = y) :
    RelIso D E :=
  (C.system D E h).isoOfEnumerations ((C.sentence_iff D E).mp h).1 C.enum C.onto b hb

end Presentation
end KnightModel.RankTwo.Scott
