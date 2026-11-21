import KnightModel.RankTwo.AmalgamationScott

/-! # Extracting orbital terms from a newly added point of relative rank one -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

variable {R : ℕ → Type} {A D : Type} {k : Nat}
variable (C : Presentation R D) (U : Model R A) (S : Model R D) (ι : Elementary U S)

private theorem label_automorphism {k} {a b : Tuple D k}
    (h : (C.label S a).Holds S b) :
    ∃ g : automorphismGroup S, ∀ i, g.val (a i) = b i := by
  let F := C.system S S (C.satisfies_self S)
  let f := F.pointedIsoOfEnumerations (s := a) (t := b) h C.enum C.onto C.enum C.onto
  exact ⟨(automorphismEquivRelIso S).symm f.val,f.property⟩

theorem label_implies_conjugate (B : Tuple D k) (x y : D)
    (h : (C.label S (push x B)).Holds S (push y B)) :
    Conjugate (automorphismGroup S) (List.ofFn B) x y := by
  obtain ⟨g,hg⟩ := label_automorphism C S h
  refine ⟨g,?_,hg 0⟩
  intro b hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
  exact hg i.succ

theorem label_unique_of_rank_zero (B : Tuple D k) (x : D)
    (h : ModelRankLE S 0 (List.ofFn B) x) (y : D) :
    (C.label S (push x B)).Holds S (push y B) ↔ y = x := by
  constructor
  · intro hy
    obtain ⟨g,hg,he⟩ := label_implies_conjugate C S B x y hy
    exact he.symm.trans (h g hg)
  · rintro rfl
    exact C.self_label S _

private theorem map_push {k} (f : A → D) (x : A) (t : Tuple A k) :
    f ∘ push x t = push (f x) (f ∘ t) := funext (Fin.cases rfl (fun _ => rfl))

include C in
/-- Even relative to additional old elements, the larger countable model can
move the new point to an old representative. -/
theorem orbit_hits_base (B : Tuple A k) (x : D) :
    ∃ y : A, Conjugate (automorphismGroup S) (List.ofFn (ι ∘ B)) x (ι y) := by
  let θ := C.label S (push x (ι ∘ B))
  have h : (Formula.ex θ).Holds S (ι ∘ B) := ⟨x,C.self_label S _⟩
  obtain ⟨y,hy⟩ := (ι.truth (.ex θ) B).mpr h
  have he := (ι.truth θ (push y B)).mp hy
  rw [map_push] at he
  exact ⟨y,label_implies_conjugate C S _ _ _ he⟩

include C in
theorem no_new_rank_zero (B : Tuple A k) (x : D) (new : ∀ y : A, ι y ≠ x) :
    ¬ ModelRankLE S 0 (List.ofFn (ι ∘ B)) x := by
  intro hx
  obtain ⟨y,g,hg,he⟩ := orbit_hits_base C U S ι B x
  exact new y (he.symm.trans (hx g hg))

/-- The portion of the marked relative orbit realized in the old model. -/
def oldOrbit (B : Tuple A k) (x : D) :=
  {y : A // Conjugate (automorphismGroup S) (List.ofFn (ι ∘ B)) x (ι y)}

/-- All old realizations of the marked orbit are individually recovered by
one-variable graph formulas over the new point and the old finite base. -/
noncomputable def terms_of_new_rank_one (B : Tuple A k) (x : D) (new : ∀ y : A, ι y ≠ x)
    (rank : ModelRankLE S 1 (List.ofFn (ι ∘ B)) x) : Terms S (oldOrbit U S ι B x) k := by
  have notLow (y : A) : ¬ ModelRankLE S 0 (ι y :: List.ofFn (ι ∘ B)) x := by
    have eqv : List.ofFn (ι ∘ push y B) = ι y :: List.ofFn (ι ∘ B) := by
      rw [map_push]
      exact List.ofFn_cons _ _
    exact eqv ▸ no_new_rank_zero C U S ι (push y B) x new
  have low (y : oldOrbit U S ι B x) : ModelRankLE S 0 (x :: List.ofFn (ι ∘ B)) (ι y.val) := by
    rcases rank with ⟨c,hc⟩ | comp
    · obtain ⟨z,hz⟩ := orbit_hits_base C U S ι B c
      exact (notLow z (hc (ι z) hz)).elim
    · exact (comp (ι y.val) y.property).resolve_left (notLow y.val)
  refine {
    base := ι ∘ B
    mark := x
    values := ⟨fun y => ι y.val,fun _ _ h => Subtype.ext (ι.toEmbedding.injective h)⟩
    graph := fun y => C.label S (push (ι y.val) (push x (ι ∘ B)))
    unique := ?_ }
  intro y z
  apply label_unique_of_rank_zero
  change ModelRankLE S 0 (List.ofFn (Fin.cons x (ι ∘ B))) (ι y.val)
  rw [List.ofFn_cons]
  exact low y

end KnightModel.RankTwo.Scott.MarkedExtension
