import KnightModel.RankTwo.NegativeTreeRows
import KnightModel.RankTwo.NegativeTreeSystem
import KnightModel.RankTwo.ScottRestrictionLabels

/-! # Interpreting the Scott-model restriction tree in finite orbit diagrams -/

namespace KnightModel.RankTwo.Scott

open Cardinal Set Restriction

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M)

include C in
/-- Rank-zero dependence composes over any base, including in the large model. -/
theorem BackAndForth.lowFiber_zero_trans (F : BackAndForth D E) {k : Nat} {t : Tuple N k} {x y z : N}
    (xy : x ∈ lowFiber F 0 (push y t)) (yz : y ∈ lowFiber F 0 (push z t)) :
    x ∈ lowFiber F 0 (push z t) := by
  obtain ⟨y₀,s,yr,hy⟩ := yz
  let base := fun i : Fin k => s i.succ
  have se : push (s 0) base = s := funext (Fin.cases rfl (fun _ => rfl))
  obtain ⟨x₀,all⟩ := F.closure.back hy x
  let sel : Fin (k+2) → Fin (k+3) := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))
  have pick := all.select F sel
  have h₁ : push x₀ (push y₀ s) ∘ sel = push x₀ (push y₀ base) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have h₂ : push x (push y (push z t)) ∘ sel = push x (push y t) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  rw [h₁,h₂] at pick
  have xr := (F.lowFiber_iff_liftRank C pick).mp xy
  rw [ofFn_push] at xr
  refine ⟨x₀,s,?_,all.eraseSecond F⟩
  intro g hg
  have ys : g • y₀ = y₀ := yr g hg
  apply xr g
  exact fixes_cons _ _ _ |>.mpr ⟨ys,fun a ha => hg a (by
    rw [← se,ofFn_push]
    exact List.mem_cons_of_mem _ ha)⟩

namespace Negative

variable (sat : BackAndForth.Satisfies E (C.sentence D))

theorem rows_transitive (e : OmegaTwo ↪ N) : TransitiveRows (rows C sat e) := by
  intro b x y z xb yb zb colxy colyz xy yz
  change witnessColor (D := D) C (color C sat (e x) (e b)) ∨ _ at xy ⊢
  change witnessColor (D := D) C (color C sat (e y) (e b)) ∨ _ at yz
  change color C sat (e x) (e b) = color C sat (e y) (e b) at colxy
  rcases xy with w | d
  · exact .inl w
  rcases yz with w | f
  · exact .inl (colxy.symm ▸ w)
  · exact .inr ((F C sat).lowFiber_zero_trans C d f)

abbrev ProfileArgs (A : Type) := (n : Nat) × Tuple A n

noncomputable def diagram {A : Type} (g : A → N) (z : N) (arg : ProfileArgs A) : Nat :=
  SentenceLabels.number C D E sat (push z (g ∘ arg.2))

/-- Rank-one colors are determined by the complete type of the ordered pair. -/
theorem color_eq {a b c d : N} (he : SentenceLabels.number C D E sat (push a (singleton b)) =
    SentenceLabels.number C D E sat (push c (singleton d))) : color C sat a b = color C sat c d := by
  apply congrArg sInf
  ext k
  apply and_congr_right
  intro _
  exact (SentenceLabels.lifts_iff C D E sat _ _).trans (((SentenceLabels.number_eq_iff C D E sat _ _).mp he _).trans
    (SentenceLabels.lifts_iff C D E sat _ _).symm)

private noncomputable def rowOn {A : Type} (g : A → N) (z : N) : Chart A where
  color i := color C sat (g i) z
  rel i j := witnessColor (D := D) C (color C sat (g i) z) ∨
    g i ∈ lowFiber (F C sat) 0 (push (g j) (singleton z))

private theorem row_eq {A : Type} {g : A → N} {z w : N}
    (same : diagram C sat g z = diagram C sat g w) : rowOn C sat g z = rowOn C sat g w := by
  have lift {m k : Nat} (arg : Tuple A m) (sel : Fin k → Fin (m+1)) :
      SentenceLabels.number C D E sat (push z (g ∘ arg) ∘ sel) =
      SentenceLabels.number C D E sat (push w (g ∘ arg) ∘ sel) :=
    SentenceLabels.number_select C D E sat (t := push z (g ∘ arg)) (u := push w (g ∘ arg))
      (congrFun same ⟨m,arg⟩) sel
  have colorSame (i : A) : color C sat (g i) z = color C sat (g i) w := by
    let sel : Fin 2 → Fin 2 := Fin.cases 1 (fun _ => 0)
    have rearrange (b : N) : push b (g ∘ singleton i) ∘ sel = push (g i) (singleton b) := by
      exact funext (Fin.cases rfl (Fin.cases rfl (fun l => l.elim0)))
    exact color_eq C sat (by simpa only [rearrange] using lift (singleton i) sel)
  apply Chart.eq_of_agreement
  · exact colorSame
  · intro i j
    change witnessColor (D := D) C (color C sat (g i) z) ∨ _ ↔ witnessColor (D := D) C (color C sat (g i) w) ∨ _
    rw [colorSame i]
    apply or_congr_right
    let sel : Fin 3 → Fin 3 := Fin.cases 1 (Fin.cases 2 (fun _ => 0))
    have rearrange (b : N) : push b (g ∘ push i (singleton j)) ∘ sel =
        push (g i) (push (g j) (singleton b)) := by exact funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun l => l.elim0))))
    apply SentenceLabels.lowFiber_congr C D E sat
    simpa only [rearrange] using lift (push i (singleton j)) sel

/-- The finite one-point diagram bound, stated on any chosen countable sequence of parameters. -/
def CountableDiagrams (O : Set N) : Prop :=
  ∀ (A : Type) [Countable A] (g : A → O),
    (range (fun b : O => diagram C sat (fun i => (g i).val) b.val)).Countable

/-- No information besides the finite one-point orbital diagram is needed to
recover a chart restricted to a countable set. -/
theorem smallTraces_of_diagrams {O : Set N} (e : OmegaTwo ↪ O) (bound : CountableDiagrams C sat O) :
    SmallTraces (rows C sat (e.trans (Function.Embedding.subtype O))) := by
  intro a X small
  let g (v : X) : O := e v.val.val
  let d (b : O) := diagram C sat (fun i => (g i).val) b.val
  let row (b : O) := rowOn C sat (fun i => (g i).val) b.val
  haveI : Countable X := small
  have dcount : (range d).Countable := bound X g
  let read (v : range d) : Chart X := row v.property.choose
  have facts : ∀ b : O, read ⟨d b,b,rfl⟩ = row b := fun b =>
    row_eq C sat ((show d ((show d b ∈ range d from ⟨b,rfl⟩).choose) = d b from
      (show d b ∈ range d from ⟨b,rfl⟩).choose_spec))
  haveI : Countable (range d) := dcount
  apply (countable_range read).mono
  rintro _ ⟨node,rfl⟩
  obtain ⟨b,ab,hb⟩ := node.property
  exact ⟨⟨d (e b),e b,rfl⟩, (facts (e b)).trans (congrArg (fun c : Chart (Iio a) => c.comap (Subtype.val : X → _)) hb.symm)⟩

theorem tree_alternative_of_diagrams (size : aleph 2 ≤ #N) (rank : ∀ x, ModelRankLE D 2 [] x)
    (bound : ∀ x : M, ℵ₁ < #(orbitFiber (F C sat) Fin.elim0 x Fin.elim0) →
      CountableDiagrams C sat (orbitFiber (F C sat) Fin.elim0 x Fin.elim0)) :
    Nonempty SpecialTree ∨ Nonempty (CountableLevelTree.{0,0,0} omegaOneStages OmegaTwo) := by
  obtain ⟨x,e,big,chain⟩ := big_skeleton C sat size rank
  let f := e.trans (Function.Embedding.subtype _)
  exact special_or_kurepa (rows_local C sat f chain) (rows_transitive C sat f)
    (smallTraces_of_diagrams C sat e (bound x big))

end Negative
end KnightModel.RankTwo.Scott
