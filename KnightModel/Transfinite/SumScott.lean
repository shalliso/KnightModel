import KnightModel.Transfinite.SumLanguage

/-! # Back-and-forth on a named ordered sum

A position carries one current finite match in each component. A global
tuple can repeat or select any of those pairs. A move enlarges a single
component's match.
-/

namespace KnightModel.Transfinite.NamedSum
open RankTwo.Scott
variable {R : ℕ → ℕ → Type} {X Y : ℕ → Type}
variable {D : ∀ i, Model (R i) (X i)} {E : ∀ i, Model (R i) (Y i)}
variable (F : ∀ i, BackAndForth (D i) (E i))

structure Position (i : ℕ) where
  n : ℕ
  left : Tuple (X i) n
  right : Tuple (Y i) n
  matched : (F i).matchTuples left right

abbrev State := ∀ i, Position F i

def Pair (p : State F) (x : Carrier X) (y : Carrier Y) : Prop :=
  ∃ i, ∃ l : Fin (p i).n, x = inject i ((p i).left l) ∧ y = inject i ((p i).right l)

variable {F}
private theorem tags {p : State F} {x y} : Pair F p x y → tag x = tag y := by
  rintro ⟨i,l,rfl,rfl⟩
  rfl

private theorem align {p : State F} {i : ℕ} {x y} (h : Pair F p x y) (hx : tag x = i) :
    ∃ l : Fin (p i).n, x = inject i ((p i).left l) ∧ y = inject i ((p i).right l) := by
  obtain ⟨j,l,rfl,rfl⟩ := h
  change j = i at hx
  subst j
  exact ⟨l,rfl,rfl⟩

private theorem same {p : State F} {x x' y y'} (h : Pair F p x y) (h' : Pair F p x' y') :
    x = x' ↔ y = y' := by
  by_cases eq : tag x' = tag x
  · obtain ⟨i,l,rfl,rfl⟩ := h
    obtain ⟨k,rfl,rfl⟩ := align h' eq
    have he := (F i).atoms (p i).matched (.eq l k)
    exact ⟨fun hh => congrArg _ (he.mp (inject_injective i hh)),
      fun hh => congrArg _ (he.mpr (inject_injective i hh))⟩
  · exact ⟨fun hh => (eq (congrArg tag hh.symm)).elim,
      fun hh => (eq ((tags h').trans ((congrArg tag hh.symm).trans (tags h).symm))).elim⟩

private theorem blocks {p : State F} {n} {s : Tuple (Carrier X) n} {t : Tuple (Carrier Y) n}
    (m : ∀ l, Pair F p (s l) (t l)) (i : ℕ) (r : R i n) :
    Block D i r s ↔ Block E i r t := by
  by_cases loc : ∀ l, tag (s l) = i
  · choose v hs ht using fun l => align (m l) (loc l)
    rw [show s = inject i ∘ ((p i).left ∘ v) from funext hs,
        show t = inject i ∘ ((p i).right ∘ v) from funext ht, onBlock, onBlock]
    exact (F i).atoms (p i).matched (.rel r v)
  · constructor
    · rintro ⟨_,h,_⟩
      exact (loc (fun l => congrArg tag (h l))).elim
    · rintro ⟨_,h,_⟩
      exact (loc (fun l => (tags (m l)).trans (congrArg tag (h l)))).elim

private theorem enlarge {p : State F} (i : ℕ) (x : X i) (y : Y i)
    (h : (F i).matchTuples (push x (p i).left) (push y (p i).right)) :
    ∃ p' : State F, Pair F p' (inject i x) (inject i y) ∧
      ∀ a b, Pair F p a b → Pair F p' a b := by
  let q : Position F i := ⟨_,_,_,h⟩
  let p' := Function.update p i q
  refine ⟨p',?_,?_⟩
  · refine ⟨i,?_⟩
    dsimp only [p']
    rw [Function.update_self]
    exact ⟨0,rfl,rfl⟩
  · rintro _ _ ⟨j,l,rfl,rfl⟩
    refine ⟨j,?_⟩
    dsimp only [p']
    by_cases eq : j = i
    · subst j
      rw [Function.update_self]
      exact ⟨l.succ,rfl,rfl⟩
    · rw [Function.update_of_ne eq]
      exact ⟨l,rfl,rfl⟩

variable (F) (leSym : ∀ i, R i 2)

def system : BackAndForth (model D leSym) (model E leSym) where
  matchTuples := fun s t => ∃ p : State F, ∀ l, Pair F p (s l) (t l)
  atoms := by
    rintro n s t ⟨p,h⟩ a
    cases a with
    | eq j k => exact same (h j) (h k)
    | rel r v =>
      cases r with
      | tag i => exact congrArg (· = i) (tags (h (v 0))) |> Iff.of_eq
      | block i r => exact blocks (fun j => h (v j)) i r
      | order =>
        change (_ < _ ∨ ∃ i, Block D i (leSym i) (s ∘ v)) ↔
          (_ < _ ∨ ∃ i, Block E i (leSym i) (t ∘ v))
        exact or_congr (by simp only [Function.comp_apply, tags (h (v 0)), tags (h (v 1))])
          (exists_congr fun i => blocks (fun j => h (v j)) i _)
  forth := by
    rintro n s t ⟨p,h⟩ ⟨i,x⟩
    obtain ⟨y,hy⟩ := (F i).forth (p i).matched x
    obtain ⟨q,hnew,hkeep⟩ := enlarge i x y hy
    exact ⟨inject i y,q,Fin.cases hnew (fun l => hkeep _ _ (h l))⟩
  back := by
    rintro n s t ⟨p,h⟩ ⟨i,y⟩
    obtain ⟨x,hx⟩ := (F i).back (p i).matched y
    obtain ⟨q,hnew,hkeep⟩ := enlarge i x y hx
    exact ⟨inject i x,q,Fin.cases hnew (fun l => hkeep _ _ (h l))⟩

theorem system_empty (empty : ∀ i, (F i).matchTuples (n := 0) Fin.elim0 Fin.elim0) :
    (system F leSym).matchTuples (n := 0) Fin.elim0 Fin.elim0 :=
  ⟨fun i => ⟨0,_,_,empty i⟩,fun l => l.elim0⟩

end KnightModel.Transfinite.NamedSum
