import KnightModel.RankTwo.MarkedExtensionFamily
import KnightModel.RankTwo.AmalgamationTwists

/-! # Relative rank-one closure in every member of a marked family -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

variable {R : Nat → Type} {M : Type} {C : Presentation R M} {D : Model R M}

private noncomputable def presentationOn (C : Presentation R M) (X : Type)
    [Nonempty X] [Countable X] : Presentation R X where
  enum := (exists_surjective_nat X).choose
  onto := (exists_surjective_nat X).choose_spec
  tuples n := (exists_surjective_nat (Tuple X n)).choose
  tuples_onto {n} := (exists_surjective_nat (Tuple X n)).choose_spec
  atoms := C.atoms
  atoms_onto := C.atoms_onto

/-- Every point of relative rank at most one over an old finite tuple in
a permitted diagram is in its old base. The new marked point is subject
to this conclusion along with all other points. -/
theorem Family.range_of_rank_one (F : Family (C.sentence D)) {B : World R}
    (p : Pointed B) (good : F.member p) {k} (b : Tuple B.carrier k) (x : p.target.carrier)
    (low : ModelRankLE p.target.model 1 (List.ofFn (p.embed ∘ b)) x) :
    x ∈ Set.range p.embed := by
  have bs := F.satisfies good
  haveI : Nonempty B.carrier :=
    let ⟨y,_⟩ := (C.system D B.model bs).forth (s := Fin.elim0) (t := Fin.elim0)
      ((C.sentence_iff D B.model).mp bs).1 (C.enum 0)
    ⟨y⟩
  haveI : Nonempty p.target.carrier := ⟨p.mark⟩
  haveI : Countable B.carrier := F.smallBase good
  haveI : Countable p.target.carrier := F.smallTarget good
  let Ct := presentationOn C p.target.carrier
  apply range_of_rank_one_of_base_changes Ct B.model p.target.model p.embed
    (presentationOn C B.carrier) b x low
  intro j
  have ts := (p.embed.sentence _).mp bs
  obtain ⟨q,_,v,square,_⟩ := F.change (E := p.target) p good inferInstance ts j
  exact ⟨q.target.carrier,q.target.model,(q.embed.sentence _).mp (Ct.satisfies_self p.target.model),
    v,q.embed,square⟩

end KnightModel.RankTwo.Scott.MarkedExtension
