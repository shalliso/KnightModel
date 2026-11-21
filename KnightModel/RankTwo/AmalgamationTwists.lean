import KnightModel.RankTwo.AmalgamationMotion
import KnightModel.RankTwo.AmalgamationCantor

/-! # Ordinary amalgamation of complete, twisted copies over the old model -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal

variable {R : ℕ → Type} {A D : Type} {k : Nat}
variable (C : Presentation R D) (U : Model R A) (S : Model R D) (ι : Elementary U S)

/-- Attach an exact copy of the countable extension along the old embedding
precomposed with the inverse of the twist. A common model must agree on
the whole old structure and may make arbitrary additional identifications. -/
def Amalgamates (g h : automorphismGroup U) : Prop :=
  ∃ (N : Type) (E : Model R N), BackAndForth.Satisfies E (C.sentence S) ∧
    ∃ l r : Elementary S E, ∀ a : A, l (ι (g.val.symm a)) = r (ι (h.val.symm a))

private theorem inverse_fixes (g : automorphismGroup U) (B : Tuple A k)
    (h : Fixes g (List.ofFn B)) (i : Fin k) : g.val.symm (B i) = B i :=
  g.val.symm_apply_eq.mpr (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).symm

theorem compatible_of_amalgamates (B : Tuple A k) (x : D) (new : ∀ y, ι y ≠ x)
    (rank : ModelRankLE S 1 (List.ofFn (ι ∘ B)) x)
    (g h : automorphismGroup U) (hg : Fixes g (List.ofFn B)) (hh : Fixes h (List.ofFn B))
    (s t : Equiv.Perm (oldOrbit U S ι B x))
    (hs : ∀ p, (s p).val = g.val p.val) (ht : ∀ p, (t p).val = h.val p.val)
    (am : Amalgamates C U S ι g h) :
    Compatible C S (terms_of_new_rank_one C U S ι B x new rank) s t := by
  obtain ⟨N,E,he,l,r,ha⟩ := am
  let j : oldOrbit U S ι B x ↪ N := {
    toFun := fun p => l (ι (g.val.symm p.val))
    inj' := fun _ _ e => Subtype.ext (g.val.symm.injective (ι.toEmbedding.injective (l.toEmbedding.injective e))) }
  refine ⟨N,⟨{
    model := E
    sentence := he
    left := l
    right := r
    base_eq := ?_
    shared := j
    left_values := ?_
    right_values := ?_ }⟩⟩
  · funext i
    change l (ι (B i)) = r (ι (B i))
    simpa only [inverse_fixes U g B hg i,inverse_fixes U h B hh i] using ha (B i)
  · intro p
    change l (ι p.val) = l (ι (g.val.symm (s p).val))
    rw [hs,g.val.symm_apply_apply]
  · intro p
    change r (ι p.val) = l (ι (g.val.symm (t p).val))
    simpa only [ht,h.val.symm_apply_apply] using (ha (t p).val).symm

/-- Turn the Cantor family of distinct restrictions into continuum many
actual automorphisms giving pairwise incompatible ordinary attachments. -/
theorem incompatible_of_cantor_restrictions (B : Tuple A k) (x : D) (new : ∀ y, ι y ≠ x)
    (rank : ModelRankLE S 1 (List.ofFn (ι ∘ B)) x)
    (w : (ℕ → Bool) ↪ Equiv.Perm (oldOrbit U S ι B x))
    (reps : ∀ b, ∃ g : automorphismGroup U, Fixes g (List.ofFn B) ∧ ∀ p, (w b p).val = g.val p.val) :
    ∃ f : (ℕ → Bool) ↪ automorphismGroup U, (∀ b, Fixes (f b) (List.ofFn B)) ∧
      Pairwise (fun b c => ¬ Amalgamates C U S ι (f b) (f c)) := by
  classical
  choose g hg lift using reps
  have size : #(ℕ → Bool) = 2 ^ ℵ₀ := by simp
  obtain ⟨F,hF,hbad⟩ := incompatible_twists C S
    (terms_of_new_rank_one C U S ι B x new rank) w size
  have gi : Function.Injective g := by
    intro i j h
    apply w.injective
    ext p
    exact Subtype.ext ((lift i p).trans (h ▸ (lift j p).symm))
  obtain ⟨e : (ℕ → Bool) ≃ F⟩ := Cardinal.eq.mp (size.trans hF.symm)
  refine ⟨⟨fun b => g (e b).val,gi.comp (Subtype.val_injective.comp e.injective)⟩,fun b => hg _,?_⟩
  intro b c ne am
  have distinct : (e b).val ≠ (e c).val := fun h => ne (e.injective (Subtype.ext h))
  exact hbad (e b).property (e c).property distinct
    (compatible_of_amalgamates C U S ι B x new rank _ _ (hg _) (hg _) _ _ (lift _) (lift _) am)

/-- A new relative-rank-one point in a countable elementary extension produces
continuum many pairwise impossible ordinary amalgamations of copies of that
very extension over the whole old model. -/
theorem continuum_twists_of_new_rank_one (C₀ : Presentation R A) (B : Tuple A k) (x : D)
    (new : ∀ y, ι y ≠ x) (rank : ModelRankLE S 1 (List.ofFn (ι ∘ B)) x) :
    ∃ f : (ℕ → Bool) ↪ automorphismGroup U, (∀ b, Fixes (f b) (List.ofFn B)) ∧
      Pairwise (fun b c => ¬ Amalgamates C U S ι (f b) (f c)) := by
  let P := {p : A | Conjugate (automorphismGroup S) (List.ofFn (ι ∘ B)) x (ι p)}
  have moves (F : Finset A) : ∃ g : automorphismGroup U, Fixes g (List.ofFn B) ∧
      (∀ y ∈ F, g.val y = y) ∧ ∃ p ∈ P, g.val p ≠ p := by
    obtain ⟨g,hg,hF,p,hm⟩ := oldOrbit_finite_motion C C₀ U S ι B x new F
    exact ⟨g,hg,hF,p.val,p.property,hm⟩
  have closed (g : automorphismGroup U) (hg : Fixes g (List.ofFn B)) (y : A) : y ∈ P ↔ g.val y ∈ P := by
    constructor
    · intro hy
      exact oldOrbit_invariant C U S ι B x g hg ⟨y,hy⟩
    · intro hy
      have hinv : Fixes g⁻¹ (List.ofFn B) := fun q hq =>
        g.val.symm_apply_eq.mpr (hg q hq).symm
      have hz := oldOrbit_invariant C U S ι B x g⁻¹ hinv ⟨g.val y,hy⟩
      exact (g.val.symm_apply_apply y) ▸ hz
  obtain ⟨w,h⟩ := cantor_restrictions_of_finite_motion U (List.ofFn B) P C₀.enum C₀.onto moves closed
  exact incompatible_of_cantor_restrictions C U S ι B x new rank w h

/-- Base change of the chosen diagram along every countable old embedding
would already have to work for copies of the same larger model. -/
def LiftsSelfBaseChanges : Prop :=
  ∀ j : Elementary U S, ∃ (N : Type) (E : Model R N),
    BackAndForth.Satisfies E (C.sentence S) ∧
    ∃ l r : Elementary S E, ∀ a, l (ι a) = r (j a)

private def twistOld (g h : automorphismGroup U) : Elementary U S where
  toEmbedding := (g.val.toEmbedding.trans h.val.symm.toEmbedding).trans ι.toEmbedding
  truth := by
    intro n φ t
    exact (aut_truth U g φ t).trans ((aut_truth U h⁻¹ φ (g.val ∘ t)).trans (ι.truth φ _))

theorem amalgamates_of_self_base_changes (lift : LiftsSelfBaseChanges C U S ι)
    (g h : automorphismGroup U) : Amalgamates C U S ι g h := by
  obtain ⟨N,E,s,l,r,agree⟩ := lift (twistOld U S ι g h)
  refine ⟨N,E,s,l,r,fun b => ?_⟩
  have he := agree (g.val.symm b)
  change l (ι (g.val.symm b)) = r (ι (h.val.symm (g.val (g.val.symm b)))) at he
  simpa only [g.val.apply_symm_apply] using he

/-- Every extension admitting arbitrary countable base changes is closed
under the relatively rank-one points over its old finite tuples. -/
theorem range_of_rank_one_of_base_changes (C₀ : Presentation R A) (B : Tuple A k) (x : D)
    (rank : ModelRankLE S 1 (List.ofFn (ι ∘ B)) x) (lift : LiftsSelfBaseChanges C U S ι) :
    x ∈ Set.range ι := by
  by_contra hn
  obtain ⟨f,_,bad⟩ := continuum_twists_of_new_rank_one C U S ι C₀ B x (fun y h => hn ⟨y,h⟩) rank
  have ne : (fun _ : ℕ => false) ≠ (fun _ : ℕ => true) := fun h => Bool.noConfusion (congrFun h 0)
  exact bad ne (amalgamates_of_self_base_changes C U S ι lift (f _) (f _))

end KnightModel.RankTwo.Scott.MarkedExtension
