import KnightModel.RankTwo.RankModel
import Mathlib.Data.Finset.Lattice.Fold

/-! # A Cantor family of restrictions of automorphisms

At a binary split, keep the current partial action and move one further point
of the distinguished set. At level n fix the nth argument and a preimage of
the nth value. Every path therefore defines an actual bijective automorphism.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Set
universe u
variable {R : ℕ → Type u} {M : Type} (D : Model R M) (B : List M) (P : Set M)

private structure State where
  auto : ↥(automorphismGroup D)
  base : Fixes auto B
  dom : Finset M

private abbrev Moves :=
  ∀ s : Finset M, ∃ g : ↥(automorphismGroup D), Fixes g B ∧
    (∀ x ∈ s, g.val x = x) ∧ ∃ p ∈ P, g.val p ≠ p

variable (chooseMove : Moves D B P)
variable (enum : ℕ → M)

private noncomputable def motion (s : State D B) := (chooseMove s.dom).choose
private noncomputable def pivot (s : State D B) : M := (chooseMove s.dom).choose_spec.2.2.choose

private noncomputable def child (s : State D B) (n : ℕ) (bit : Bool) : State D B := by
  classical
  let g := if bit then s.auto * motion D B P chooseMove s else s.auto
  have base : Fixes g B := by
    intro x hx
    cases bit with
    | false => exact s.base x hx
    | true =>
      change s.auto.val ((motion D B P chooseMove s).val x) = x
      rw [show (motion D B P chooseMove s).val x = x from (chooseMove s.dom).choose_spec.1 x hx]
      exact s.base x hx
  exact ⟨g, base, insert (pivot D B P chooseMove s)
    (insert (enum n) (insert (g.val.symm (enum n)) s.dom))⟩

private theorem child_preserves (s : State D B) (n : ℕ) (bit : Bool) {x : M}
    (hx : x ∈ s.dom) : x ∈ (child D B P chooseMove enum s n bit).dom ∧
    (child D B P chooseMove enum s n bit).auto.val x = s.auto.val x := by
  classical
  refine ⟨by simp [child,hx], ?_⟩
  cases bit with
  | false => rfl
  | true =>
    change s.auto.val ((motion D B P chooseMove s).val x) = s.auto.val x
    exact congrArg s.auto.val ((chooseMove s.dom).choose_spec.2.1 x hx)

private noncomputable def path (b : ℕ → Bool) : ℕ → State D B
  | 0 => ⟨1, fun _ _ => rfl, ∅⟩
  | n + 1 => child D B P chooseMove enum (path b n) n (b n)

private theorem keeps (b : ℕ → Bool) {n k : ℕ} (h : n ≤ k) {x : M}
    (hx : x ∈ (path D B P chooseMove enum b n).dom) :
    x ∈ (path D B P chooseMove enum b k).dom ∧
    (path D B P chooseMove enum b k).auto.val x = (path D B P chooseMove enum b n).auto.val x := by
  induction h with
  | refl => exact ⟨hx,rfl⟩
  | @step m h ih =>
    have s := child_preserves D B P chooseMove enum (path D B P chooseMove enum b m) m (b m) ih.1
    exact ⟨s.1,s.2.trans ih.2⟩

variable (onto : Function.Surjective enum)

private noncomputable def branchMap (b : ℕ → Bool) (x : M) : M :=
  (path D B P chooseMove enum b ((onto x).choose + 1)).auto.val x

private theorem scheduled (b : ℕ → Bool) (x : M) :
    x ∈ (path D B P chooseMove enum b ((onto x).choose + 1)).dom := by
  classical
  have he := (onto x).choose_spec
  simp only [path, child, Finset.mem_insert]
  exact Or.inr (Or.inl he.symm)

private theorem agrees (b : ℕ → Bool) (n : ℕ) (x : M)
    (hx : x ∈ (path D B P chooseMove enum b n).dom) :
    branchMap D B P chooseMove enum onto b x = (path D B P chooseMove enum b n).auto.val x := by
  let i := (onto x).choose + 1
  have left := keeps D B P chooseMove enum b (Nat.le_max_left i n)
    (scheduled D B P chooseMove enum onto b x)
  have right := keeps D B P chooseMove enum b (Nat.le_max_right i n) hx
  exact left.2.symm.trans right.2

private theorem agrees_finitely (b : ℕ → Bool) {k} (t : Tuple M k) :
    ∃ n, ∀ i, branchMap D B P chooseMove enum onto b (t i) =
        (path D B P chooseMove enum b n).auto.val (t i) := by
  classical
  let level (i : Fin k) := (onto (t i)).choose + 1
  let n := Finset.univ.sup level
  refine ⟨n, fun i => ?_⟩
  apply agrees
  exact (keeps D B P chooseMove enum b (show level i ≤ n from Finset.le_sup (Finset.mem_univ i))
    (scheduled D B P chooseMove enum onto b (t i))).1

private theorem branch_bijective (b : ℕ → Bool) :
    Function.Bijective (branchMap D B P chooseMove enum onto b) := by
  constructor
  · intro x y h
    let t : Tuple M 2 := Fin.cases x (fun _ => y)
    obtain ⟨n, he⟩ := agrees_finitely D B P chooseMove enum onto b t
    exact (path D B P chooseMove enum b n).auto.val.injective ((he 0).symm.trans (h.trans (he 1)))
  · intro y
    obtain ⟨n,rfl⟩ := onto y
    let s := path D B P chooseMove enum b (n+1)
    let x := s.auto.val.symm (enum n)
    have mem : x ∈ s.dom := by
      classical
      simp only [x, s, path, child, Finset.mem_insert]
      exact Or.inr (Or.inr (Or.inl trivial))
    exact ⟨x, (agrees D B P chooseMove enum onto b (n+1) x mem).trans (s.auto.val.apply_symm_apply _)⟩

private noncomputable def branchAuto (b : ℕ → Bool) : ↥(automorphismGroup D) :=
  ⟨Equiv.ofBijective _ (branch_bijective D B P chooseMove enum onto b), by
    intro k r t
    obtain ⟨n, hn⟩ := agrees_finitely D B P chooseMove enum onto b t
    exact ((path D B P chooseMove enum b n).auto.property r t).trans
      (iff_of_eq (congrArg (D r) (funext (fun i => (hn i).symm))))⟩

private theorem branch_fixes (b : ℕ → Bool) : Fixes (branchAuto D B P chooseMove enum onto b) B :=
  fun x hx => (path D B P chooseMove enum b ((onto x).choose + 1)).base x hx

private theorem prefix_state (b c : ℕ → Bool) (n : ℕ) (h : ∀ i < n, b i = c i) :
    path D B P chooseMove enum b n = path D B P chooseMove enum c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [path,path,ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),h n (Nat.lt_succ_self n)]

private theorem distinguish (b c : ℕ → Bool) (h : b ≠ c) :
    ∃ p ∈ P, (branchAuto D B P chooseMove enum onto b).val p ≠
      (branchAuto D B P chooseMove enum onto c).val p := by
  classical
  have existsDiff : ∃ i, b i ≠ c i := by
    by_contra! eq
    exact h (funext eq)
  let n := Nat.find existsDiff
  let s := path D B P chooseMove enum b n
  have same : path D B P chooseMove enum c n = s := (prefix_state D B P chooseMove enum b c n
    (fun i hi => not_not.mp (Nat.find_min existsDiff hi))).symm
  let p := pivot D B P chooseMove s
  have hp := (chooseMove s.dom).choose_spec.2.2.choose_spec
  have mem (bit : Bool) : p ∈ (child D B P chooseMove enum s n bit).dom := Finset.mem_insert_self ..
  have hb := agrees D B P chooseMove enum onto b (n+1) p (mem (b n))
  have hc := agrees D B P chooseMove enum onto c (n+1) p (by simpa only [path,same] using mem (c n))
  refine ⟨p, hp.1, ?_⟩
  change branchMap D B P chooseMove enum onto b p ≠ branchMap D B P chooseMove enum onto c p
  rw [hb,hc]
  change (child D B P chooseMove enum s n (b n)).auto.val p ≠
    (child D B P chooseMove enum (path D B P chooseMove enum c n) n (c n)).auto.val p
  rw [same]
  have ne : b n ≠ c n := Nat.find_spec existsDiff
  cases eb : b n <;> cases ec : c n
  · exact False.elim (ne (eb.trans ec.symm))
  · exact fun eq => hp.2 (s.auto.val.injective eq).symm
  · exact fun eq => hp.2 (s.auto.val.injective eq)
  · exact False.elim (ne (eb.trans ec.symm))

/-- Infinitely much motion over every finite control set gives continuum
many distinct restrictions of actual automorphisms fixing the finite base. -/
theorem cantor_restrictions_of_finite_motion (enum : ℕ → M) (onto : Function.Surjective enum)
    (moves : ∀ s : Finset M, ∃ g : ↥(automorphismGroup D), Fixes g B ∧
      (∀ x ∈ s, g.val x = x) ∧ ∃ p ∈ P, g.val p ≠ p)
    (pres : ∀ g : ↥(automorphismGroup D), Fixes g B → ∀ x, x ∈ P ↔ g.val x ∈ P) :
    ∃ e : (ℕ → Bool) ↪ Equiv.Perm P, ∀ b, ∃ g : ↥(automorphismGroup D),
      Fixes g B ∧ ∀ p : P, (e b p).val = g.val p.val := by
  let g := branchAuto D B P moves enum onto
  have hg := branch_fixes D B P moves enum onto
  let r (b : ℕ → Bool) : Equiv.Perm P := (g b).val.subtypeEquiv (pres (g b) (hg b))
  have inj : Function.Injective r := by
    intro b c he
    by_contra hbc
    obtain ⟨p, hp, ne⟩ := distinguish D B P moves enum onto b c hbc
    exact ne (congrArg (fun e : Equiv.Perm P => (e ⟨p,hp⟩).val) he)
  exact ⟨⟨r,inj⟩, fun b => ⟨g b,hg b,fun _ => rfl⟩⟩

end KnightModel.RankTwo.Scott.MarkedExtension
