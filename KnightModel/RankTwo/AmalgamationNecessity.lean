import KnightModel.RankTwo.ScottSubcopy
import KnightModel.RankTwo.NegativeTreeRows
import KnightModel.RankTwo.AmalgamationRank

/-! # Every positive example supplies a marked countable proper extension

The ω₂-comparison sequence has an endpoint above an ω₁-long initial
subsequence. A countable elementary copy containing that endpoint misses
one of those lower points. A second countable copy contains both.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal Set Restriction
variable {R : ℕ → Type} {M N : Type} {D : Model R M} {E : Model R N}
variable (C : Presentation R M) (sat : BackAndForth.Satisfies E (C.sentence D))

private theorem long_prefix : ∃ (b : OmegaTwo) (f : OmegaOne ↪ OmegaTwo), ∀ i, f i < b := by
  let h : (aleph.{0} 1).ord < (aleph 2).ord := ord_lt_ord.mpr (aleph_lt_aleph.mpr _root_.one_lt_two)
  let incl : Iio (aleph.{0} 1).ord ↪ Iio (aleph 2).ord :=
    ⟨fun i => ⟨i.val,i.property.trans h⟩,fun _ _ e => Subtype.ext (congrArg (fun v : Iio (aleph.{0} 2).ord => v.val) e)⟩
  let f := Ordinal.ToType.mk.symm.toEquiv.toEmbedding.trans (incl.trans Ordinal.ToType.mk.toEquiv.toEmbedding)
  exact ⟨Ordinal.ToType.mk ⟨_,h⟩,f,fun i =>
    Ordinal.ToType.mk.strictMono (show (incl i.toOrd).val < (aleph 1).ord from i.toOrd.property)⟩

private theorem outside {S : Set N} (small : S.Countable) (f : OmegaOne ↪ N) : ∃ i, f i ∉ S := by
  by_contra! h
  haveI : Countable S := small
  let g (i : OmegaOne) : S := ⟨f i,h i⟩
  have inj : Function.Injective g := fun _ _ e => f.injective (congrArg Subtype.val e)
  haveI : Countable OmegaOne := inj.countable
  have hc := mk_le_aleph0 (α := OmegaOne)
  exact aleph0_lt_aleph_one.not_ge (by simpa only [mk_toType,card_ord] using hc)

include C sat in
/-- Countable copies of the same Scott model, one containing a new low point
over a singleton of the old copy, can be presented by a proper elementary
self-embedding of the original countable structure. -/
theorem new_rank_one_extension (size : aleph 2 ≤ #N) (rank : ∀ x, ModelRankLE D 2 [] x) :
    ∃ (emb : Elementary D D) (b x : M), x ∉ range emb ∧ ModelRankLE D 1 [emb b] x := by
  classical
  obtain ⟨a,e,big,chain⟩ := Negative.big_skeleton C sat size rank
  obtain ⟨β,f,below⟩ := long_prefix
  let base : N := (e β).val
  obtain ⟨S,incS,sc,closedS⟩ := LabelClosed.exists_countable C sat (countable_singleton base)
  have bs : base ∈ S := incS (mem_singleton base)
  let intoN := f.trans (e.trans (Function.Embedding.subtype _))
  obtain ⟨i,miss⟩ := outside sc intoN
  let mark := intoN i
  have mr : mark ∈ lowFiber (C.system D E sat) 1 (Negative.singleton base) :=
    chain _ _ (below i)
  obtain ⟨T,incT,tc,closedT⟩ := LabelClosed.exists_countable C sat (sc.insert mark)
  have st : S ⊆ T := fun _ hb => incT (mem_insert_of_mem _ hb)
  have mt : mark ∈ T := incT (mem_insert _ _)
  let bS : S := ⟨base,bs⟩
  let bT : T := ⟨base,st bs⟩
  let xT : T := ⟨mark,mt⟩
  let smallModel : Model R S := inducedModel E S
  let bigModel : Model R T := inducedModel E T
  haveI : Nonempty S := ⟨bS⟩
  haveI : Nonempty T := ⟨bT⟩
  haveI : Countable S := sc
  haveI : Countable T := tc
  obtain ⟨enumS,ontoS⟩ := exists_surjective_nat S
  obtain ⟨enumT,ontoT⟩ := exists_surjective_nat T
  let smallIso := C.isoOfSatisfies D smallModel (LabelClosed.satisfies C sat closedS) enumS ontoS
  have satisfiesT := LabelClosed.satisfies C sat closedT
  obtain ⟨x,s,xrank,xtype⟩ := mr
  let t := push xT (Negative.singleton bT)
  have ambient := (SentenceLabels.lifts_iff C D E sat _ _).mp xtype
  have ambientTuple : (Subtype.val : T → N) ∘ t = push mark (Negative.singleton base) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun k => k.elim0)))
  have ht : (C.label D (push x s)).Holds bigModel t :=
    ((LabelClosed.elementary C sat closedT).truth _ t).mpr (ambientTuple ▸ ambient)
  let bigIso := (C.system D bigModel satisfiesT).pointedIsoOfEnumerations
    (s := push x s) (t := t) ht C.enum C.onto enumT ontoT
  let inc := LabelClosed.inclusion C sat closedS closedT st
  let emb := (smallIso.elementary.comp inc).comp bigIso.val.elementaryInverse
  let b := smallIso.invFun bS
  have atBase : emb b = s 0 := by
    change bigIso.val.invFun (inc (smallIso.toFun (smallIso.invFun bS))) = s 0
    rw [smallIso.rightInv]
    change bigIso.val.invFun bT = s 0
    have hb : bigIso.val.toFun (s 0) = bT := bigIso.property (0 : Fin 1).succ
    rw [← hb,bigIso.val.leftInv]
  refine ⟨emb,b,x,?_,?_⟩
  · rintro ⟨z,hz⟩
    have h : bigIso.val.invFun (inc (smallIso.toFun z)) = x := hz
    have eh : inc (smallIso.toFun z) = xT := by
      rw [← bigIso.val.rightInv (inc (smallIso.toFun z)),h]
      exact bigIso.property 0
    have val : (smallIso.toFun z).val = mark := congrArg Subtype.val eh
    apply miss
    change mark ∈ S
    rw [← val]
    exact (smallIso.toFun z).property
  · rw [atBase]
    simpa [List.ofFn_succ] using xrank

end KnightModel.RankTwo.Scott.MarkedExtension
