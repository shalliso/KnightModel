import KnightModel.RankTwo.MarkedExtensionDiagrams
import KnightModel.RankTwo.ScottResolution

/-! # Countable marked extensions over elementary submodels of a fixed base -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Set Cardinal

variable {R : Nat → Type} {M : Type} {C : Presentation R M} {D : Model R M}

/-- Factor a surjective elementary inclusion backwards. -/
noncomputable def Elementary.inverse {X Y : Type} {U : Model R X} {V : Model R Y}
    (f : Elementary U V) (onto : Function.Surjective f) : Elementary V U where
  toEmbedding := (Equiv.ofBijective _ ⟨f.injective,onto⟩).symm.toEmbedding
  truth := by
    intro n φ t
    let e := Equiv.ofBijective _ ⟨f.injective,onto⟩
    have eq : f ∘ (e.symm ∘ t) = t := funext (fun i => e.apply_symm_apply _)
    have h := (f.truth φ (e.symm ∘ t)).symm
    rw [eq] at h
    exact h

theorem Family.existsOver (F : Family (C.sentence D)) (E : World R)
    (sc : Countable E.carrier) (sat : BackAndForth.Satisfies E.model (C.sentence D)) :
    ∃ q : Pointed E, F.member q := by
  obtain ⟨B,p,hp⟩ := F.seed
  have bs := F.satisfies hp
  haveI : Countable B.carrier := F.smallBase hp
  haveI : Nonempty B.carrier :=
    let ⟨y,_⟩ := (C.system D B.model bs).forth (s := Fin.elim0) (t := Fin.elim0) ((C.sentence_iff D B.model).mp bs).1 (C.enum 0)
    ⟨y⟩
  haveI : Nonempty E.carrier :=
    let ⟨y,_⟩ := (C.system D E.model sat).forth (s := Fin.elim0) (t := Fin.elim0) ((C.sentence_iff D E.model).mp sat).1 (C.enum 0)
    ⟨y⟩
  obtain ⟨b,hb⟩ := exists_surjective_nat B.carrier
  obtain ⟨e,he⟩ := exists_surjective_nat E.carrier
  let f := (C.isoOfSatisfies D B.model bs b hb).elementaryInverse.comp
    (C.isoOfSatisfies D E.model sat e he).elementary
  obtain ⟨q,hq,_⟩ := F.change p hp sc sat f
  exact ⟨q,hq⟩

def subworld (B : World R) (S : Set B.carrier) : World R := ⟨S,inducedModel B.model S⟩

/-- Objects are marked extensions over countable closed subsets of one fixed
ambient Scott model. -/
structure LocalStage (F : Family (C.sentence D)) (B : World R)
    (sat : BackAndForth.Satisfies B.model (C.sentence D)) where
  support : Set B.carrier
  small : support.Countable
  closed : LabelClosed C sat support
  point : Pointed (subworld B support)
  good : F.member point

namespace LocalStage

variable {F : Family (C.sentence D)} {B : World R}
variable {sat : BackAndForth.Satisfies B.model (C.sentence D)}

/-- An arrow is literal inclusion on the base and an elementary embedding on
the upper model preserving the marked point. -/
structure Arrow (a b : LocalStage F B sat) where
  sub : a.support ⊆ b.support
  upper : Elementary a.point.target.model b.point.target.model
  comm : ∀ x, upper (a.point.embed x) = b.point.embed ⟨x.val,sub x.property⟩
  keep : upper a.point.mark = b.point.mark

def compose {a b c : LocalStage F B sat} (f : Arrow a b) (g : Arrow b c) : Arrow a c where
  sub := f.sub.trans g.sub
  upper := f.upper.comp g.upper
  comm := fun x => (congrArg g.upper (f.comm x)).trans (g.comm _)
  keep := (congrArg g.upper f.keep).trans g.keep

theorem Arrow.ext {a b : LocalStage F B sat} {f g : Arrow a b}
    (eq : ∀ x, f.upper x = g.upper x) : f = g := by
  cases f with
  | mk s f hf mf =>
    cases g with
    | mk t g hg mg =>
      have h : f = g := by
        cases f
        cases g
        congr 1
        exact Function.Embedding.ext eq
      cases h
      rfl

end LocalStage
end KnightModel.RankTwo.Scott.MarkedExtension
