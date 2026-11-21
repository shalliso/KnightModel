import KnightModel.RankTwo.AmalgamationRank

/-! # Finite motion on the old part of a newly realized orbit -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

variable {R : ℕ → Type} {A D : Type} {k : Nat}
variable (C : Presentation R D) (C₀ : Presentation R A) (U : Model R A) (S : Model R D)
    (ι : Elementary U S)

private theorem movedPush {X Y : Type} {n} (f : X → Y) (x : X) (t : Tuple X n) :
    f ∘ push x t = push (f x) (f ∘ t) := funext (Fin.cases rfl (fun _ => rfl))

/-- Automorphisms preserve every formula of the countable infinitary syntax. -/
theorem aut_truth (g : automorphismGroup U) {n} (φ : Formula R n) (t : Tuple A n) :
    φ.Holds U t ↔ φ.Holds U (g.val ∘ t) := by
  induction φ with
  | top => rfl
  | atom a =>
    cases a with
    | eq i j => exact g.val.injective.eq_iff.symm
    | rel r v => exact g.property r (t ∘ v)
  | neg f ih => exact not_congr (ih _)
  | conj f ih => exact forall_congr' fun i => ih i t
  | ex φ ih =>
    constructor
    · rintro ⟨x,h⟩
      exact ⟨g.val x,movedPush g.val x t ▸ (ih (push x t)).mp h⟩
    · rintro ⟨y,h⟩
      obtain ⟨x,rfl⟩ := g.val.surjective y
      exact ⟨x,(ih (push x t)).mpr (movedPush g.val x t ▸ h)⟩

private theorem map_fixed {X : Type} (U : Model R X) (g : automorphismGroup U)
    {n} (B : Tuple X n) (h : Fixes g (List.ofFn B)) : g.val ∘ B = B :=
  funext fun i => h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem conjugate_iff_label (B : Tuple D k) (x y : D) :
    Conjugate (automorphismGroup S) (List.ofFn B) x y ↔
      (C.label S (push x B)).Holds S (push y B) := by
  refine ⟨?_, label_implies_conjugate C S B x y⟩
  rintro ⟨g,hg,rfl⟩
  have h := (aut_truth S g _ (push x B)).mp (C.self_label S (push x B))
  rw [movedPush,map_fixed S g B hg] at h
  exact h

include C in
/-- The old stabilizer acts on the set of points whose images are in the
relative orbit of the new point. No automorphism of the old model needs to
extend to the larger model. -/
theorem oldOrbit_invariant (B : Tuple A k) (x : D) (g : automorphismGroup U)
    (hg : Fixes g (List.ofFn B)) (p : oldOrbit U S ι B x) :
    Conjugate (automorphismGroup S) (List.ofFn (ι ∘ B)) x (ι (g.val p.val)) := by
  let φ := C.label S (push x (ι ∘ B))
  have h := ((conjugate_iff_label C S _ x _).mp p.property)
  have ht : φ.Holds U (push p.val B) := (ι.truth φ _).mpr (movedPush ι p.val B ▸ h)
  have moved := (aut_truth U g φ (push p.val B)).mp ht
  rw [movedPush,map_fixed U g B hg] at moved
  have he := (ι.truth φ _).mp moved
  rw [movedPush] at he
  exact (conjugate_iff_label C S _ x _).mpr he

include C C₀ in
/-- Every finite old stabilizer moves some point of the old part of the
new orbit. This already follows from elementarity and newness alone. -/
theorem oldOrbit_finite_motion (B : Tuple A k) (x : D) (new : ∀ y, ι y ≠ x) (F : Finset A) :
    ∃ g : automorphismGroup U, Fixes g (List.ofFn B) ∧ (∀ y ∈ F, g.val y = y) ∧
      ∃ p : oldOrbit U S ι B x, g.val p.val ≠ p.val := by
  classical
  let L := List.ofFn B ++ F.toList
  let T := L.get
  have ofT : List.ofFn T = L := List.ofFn_get L
  have mapT : List.ofFn (ι ∘ T) = L.map ι := by rw [← List.map_ofFn,ofT]
  obtain ⟨y,g,hfix,he⟩ := orbit_hits_base C U S ι T x
  have fB : Fixes g (List.ofFn (ι ∘ B)) := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    apply hfix
    rw [mapT]
    exact List.mem_map.mpr ⟨B i,List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩),rfl⟩
  let p : oldOrbit U S ι B x := ⟨y,g,fB,he⟩
  have moves : ¬ ModelRankLE U 0 (List.ofFn T) y := by
    intro hy
    let ψ := C₀.label U (push y T)
    have unique (z : D) : ψ.Holds S (push z (ι ∘ T)) ↔ z = ι y :=
      ι.unique_fiber ψ T y (label_unique_of_rank_zero C₀ U T y hy) z
    have hx := (aut_truth S g ψ (push x (ι ∘ T)))
    rw [movedPush,map_fixed S g _ hfix,show g.val x = ι y from he] at hx
    exact new y ((unique x).mp (hx.mpr ((unique _).mpr rfl))).symm
  change ¬ ∀ f : automorphismGroup U, Fixes f (List.ofFn T) → f.val y = y at moves
  push Not at moves
  obtain ⟨f,hf,hn⟩ := moves
  rw [ofT] at hf
  exact ⟨f,(fun t h => hf t (List.mem_append_left _ h)),
    (fun z h => hf z (List.mem_append_right _ (Finset.mem_toList.mpr h))),p,hn⟩

end KnightModel.RankTwo.Scott.MarkedExtension
