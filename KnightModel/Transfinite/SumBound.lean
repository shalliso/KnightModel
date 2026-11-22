import KnightModel.Transfinite.SumLanguage

/-! # Cardinal bound for every Scott realization of a named sum -/

namespace KnightModel.Transfinite.NamedSum
open RankTwo.Scott Cardinal
variable {R : ℕ → ℕ → Type} {X : ℕ → Type} {N : Type}
variable {D : ∀ i, Model (R i) (X i)} {leSym : ∀ i, R i 2}
variable (U : Model (Relation R) N)

abbrev Fiber (i : ℕ) := {x : N // U (.tag i) (fun _ => x)}
def fiberModel (i : ℕ) : Model (R i) (Fiber U i) :=
  fun r v => U (.block i r) (Subtype.val ∘ v)

private theorem comp_push {A B : Type} (f : A → B) {n} (x : A) (s : Tuple A n) :
    f ∘ push x s = push (f x) (f ∘ s) := funext (Fin.cases rfl (fun _ => rfl))

variable {U}
def project (F : BackAndForth (model D leSym) U) (i : ℕ) :
    BackAndForth (D i) (fiberModel U i) where
  matchTuples := fun s t => F.matchTuples (inject i ∘ s) (Subtype.val ∘ t)
  atoms := by
    intro n s t h a
    cases a with
    | eq j k =>
      have hv := F.atoms h (.eq j k)
      exact ⟨fun e => Subtype.ext (hv.mp (congrArg (inject i) e)),
        fun e => inject_injective _ (hv.mpr (congrArg Subtype.val e))⟩
    | rel r v =>
      have hv := F.atoms h (.rel (.block i r) v)
      exact (onBlock (R := R) D i r (s ∘ v)).symm.trans hv
  forth := by
    intro n s t h x
    obtain ⟨y,hy⟩ := F.forth h (inject i x)
    have mem : U (.tag i) (fun _ => y) := (F.atoms hy (.rel (.tag i) (fun _ => 0))).mp rfl
    refine ⟨⟨y,mem⟩,?_⟩
    rw [comp_push, comp_push (fun z : Fiber U i => z.val)]
    exact hy
  back := by
    intro n s t h y
    obtain ⟨⟨j,x⟩,hx⟩ := F.back h y.val
    have eq : j = i := (F.atoms hx (.rel (.tag i) (fun _ => 0))).mpr y.property
    subst j
    refine ⟨x,?_⟩
    rw [comp_push, comp_push (fun z : Fiber U i => z.val)]
    exact hx

theorem project_empty (F : BackAndForth (model D leSym) U)
    (h : F.matchTuples (n := 0) Fin.elim0 Fin.elim0) (i : ℕ) :
    (project F i).matchTuples (n := 0) Fin.elim0 Fin.elim0 := by
  change F.matchTuples _ _
  convert h using 1

theorem all_fibers (F : BackAndForth (model D leSym) U)
    (h : F.matchTuples (n := 0) Fin.elim0 Fin.elim0) (y : N) :
    ∃ i, U (.tag i) (fun _ => y) := by
  obtain ⟨⟨i,x⟩,hm⟩ := F.back h y
  exact ⟨i,(F.atoms hm (.rel (.tag i) (fun _ => 0))).mp rfl⟩

theorem sum_size_le (A : ℕ → Type) {κ : Cardinal} (inf : ℵ₀ ≤ κ)
    (hk : ∀ i, #(A i) ≤ κ) : #(Σ i, A i) ≤ κ := by
  calc
    _ = Cardinal.sum (fun i => #(A i)) := mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ℕ => κ) := sum_le_sum _ _ hk
    _ = κ := by simp [Cardinal.sum_const, Cardinal.mul_eq_max, inf]

theorem bound (F : BackAndForth (model D leSym) U)
    (h : F.matchTuples (n := 0) Fin.elim0 Fin.elim0) {κ : Cardinal}
    (inf : ℵ₀ ≤ κ) (hk : ∀ i, #(Fiber U i) ≤ κ) : #N ≤ κ := by
  choose slot member using all_fibers F h
  let locate (y : N) : Σ i, Fiber U i := ⟨slot y, ⟨y,member y⟩⟩
  have inj : Function.Injective locate := fun _ _ eq => congrArg (fun v => v.2.val) eq
  exact (mk_le_of_injective inj).trans (sum_size_le _ inf hk)

end KnightModel.Transfinite.NamedSum
