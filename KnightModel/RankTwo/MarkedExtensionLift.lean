import KnightModel.RankTwo.MarkedExtensionFamily
import KnightModel.RankTwo.MarkedExtensionStrict

/-! # Lifting a marked countable family over an arbitrary ℵ₁-sized base -/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Set Cardinal Transfinite Restriction

variable {R : Nat → Type} {M : Type} {C : Presentation R M} {D : Model R M}

namespace LocalStage

variable {F : Family (C.sentence D)} {B : World R}
variable {sat : BackAndForth.Satisfies B.model (C.sentence D)}
variable {J : Type} [LinearOrder J]

abbrev System (F : Family (C.sentence D)) (B : World R)
    (sat : BackAndForth.Satisfies B.model (C.sentence D)) (J : Type) [LinearOrder J] :=
  Diagram (Arrow (F := F) (B := B) (sat := sat)) compose J

variable (L : System F B sat J)

private def lower {a b : LocalStage F B sat} (f : Arrow a b) :
    Elementary (subworld B a.support).model (subworld B b.support).model :=
  LabelClosed.inclusion C sat a.closed b.closed f.sub

private def baseTower : Tower R J :=
  ofStrict L (fun a => subworld B a.support) (fun f => lower f) (fun _ _ _ => rfl)

private def topTower : Tower R J :=
  ofStrict L (fun a => a.point.target) (fun f => f.upper) (fun _ _ _ => rfl)

private theorem base_lt {i j : J} (h : i < j) :
    (baseTower L).map h.le = lower (L.map h) :=
  ofStrict_map_lt L _ _ (fun _ _ _ => rfl) h

private theorem top_lt {i j : J} (h : i < j) :
    (topTower L).map h.le = (L.map h).upper :=
  ofStrict_map_lt L _ _ (fun _ _ _ => rfl) h

def chain : MarkedChain R J where
  base := baseTower L
  top := topTower L
  embed i := (L.obj i).point.embed
  mark i := (L.obj i).point.mark
  fresh i := (L.obj i).point.fresh
  comm := by
    intro i j h x
    rcases h.eq_or_lt with rfl | hi
    · rw [Tower.id_map,Tower.id_map]
    · change (topTower L).map _ ((L.obj i).point.embed x) = (L.obj j).point.embed ((baseTower L).map _ x)
      rw [top_lt L hi,base_lt L hi]
      exact (L.map hi).comm x
  keep := by
    intro i j h
    rcases h.eq_or_lt with rfl | hi
    · exact (topTower L).id_map _ _
    · rw [top_lt L hi]
      exact (L.map hi).keep

theorem map_val {i j : J} (h : i ≤ j) (x : (L.obj i).support) :
    (((chain L).base.map h x) : (L.obj j).support).val = x.val := by
  rcases h.eq_or_lt with rfl | hi
  · rw [Tower.id_map]
  · change (((baseTower L).map (i := i) (j := j) h x) : (L.obj j).support).val = _
    rw [base_lt L hi]
    rfl

theorem all_good (i : J) : F.member ((chain L).stage i) := (L.obj i).good

/-- The upper union still lies over the original base once the countable
supports exhaust it. No extra amalgamation property is needed. -/
theorem finish [Nonempty J] (size : #J ≤ ℵ₁)
    (cover : ∀ x : B.carrier, ∃ i, x ∈ (L.obj i).support) :
    ∃ q : Pointed B, #q.target.carrier ≤ ℵ₁ := by
  let e (i : J) := LabelClosed.elementary C sat (L.obj i).closed
  have comm (i j : J) (h : i ≤ j) (x : (L.obj i).support) :
      e i x = e j ((chain L).base.map h x) := (map_val L h x).symm
  let u : Elementary (chain L).base.limit.model B.model := (chain L).base.descend e comm
  have onto : Function.Surjective u := by
    intro x
    obtain ⟨i,mem⟩ := cover x
    exact ⟨(chain L).base.into i ⟨x,mem⟩,rfl⟩
  let p := (chain L).union
  let q : Pointed B := {
    target := p.target
    embed := (u.inverse onto).comp p.embed
    mark := p.mark
    fresh := fun x => p.fresh _ }
  refine ⟨q,(chain L).top.mk_limit_le _ (aleph0_le_aleph 1) size ?_⟩
  intro i
  haveI : Countable (L.obj i).point.target.carrier := F.smallTarget (L.obj i).good
  exact (mk_le_aleph0 (α := (L.obj i).point.target.carrier)).trans (aleph0_le_aleph 1)

/-- Enlarge the old supports to a single countable elementary subcopy
containing one more specified level of the resolution. -/
theorem next [Countable J] [WellFoundedLT J] {S : Set B.carrier} (small : S.Countable) :
    ∃ a : Apex Arrow compose L, S ⊆ a.obj.support := by
  classical
  let U := S ∪ ⋃ i, (L.obj i).support
  have usc : U.Countable := small.union (countable_iUnion (fun i => (L.obj i).small))
  obtain ⟨V,inc,vc,closed⟩ := LabelClosed.exists_countable C sat usc
  have subs (i : J) : (L.obj i).support ⊆ V := fun x hx => inc (Or.inr (mem_iUnion.mpr ⟨i,hx⟩))
  let B' := subworld B V
  have sats : BackAndForth.Satisfies B'.model (C.sentence D) := LabelClosed.satisfies C sat closed
  have sin : S ⊆ V := fun x hx => inc (Or.inl hx)
  by_cases ne : Nonempty J
  · letI := ne
    let Z := (chain L)
    let incl (i : J) := LabelClosed.inclusion C sat (L.obj i).closed closed (subs i)
    have comm (i j : J) (h : i ≤ j) (x : (L.obj i).support) :
        incl i x = incl j (Z.base.map h x) := Subtype.ext ((map_val L h x).symm)
    let e : Elementary Z.base.limit.model B'.model := Z.base.descend incl comm
    obtain ⟨q,hq,f,square,mark⟩ := F.change (E := B') Z.union (F.closed Z (all_good L)) vc sats e
    let a : LocalStage F B sat := ⟨V,vc,closed,q,hq⟩
    let leg (i : J) : Arrow (L.obj i) a := {
      sub := subs i
      upper := (Z.top.into i).comp f
      comm := fun x => square (Z.base.into i x)
      keep := (congrArg f (Z.union_mark i)).trans mark }
    refine ⟨⟨a,leg,?_⟩,sin⟩
    intro i j h
    apply Arrow.ext
    intro x
    change f (Z.top.into j ((L.map h).upper x)) = f (Z.top.into i x)
    apply congrArg f
    exact ofStrict_into_map_lt L (fun a => a.point.target) (fun f => f.upper) (fun _ _ _ => rfl) h x
  · obtain ⟨q,hq⟩ := F.existsOver B' vc sats
    let a : LocalStage F B sat := ⟨V,vc,closed,q,hq⟩
    exact ⟨⟨a,fun i => (ne ⟨i⟩).elim,fun {i} {_} _ => (ne ⟨i⟩).elim⟩,sin⟩

end LocalStage

/-- Any model of the Scott sentence of size at most ℵ₁ has a proper
elementary extension of size at most ℵ₁, with one point outside its image. -/
theorem Family.extend (C : Presentation R M) (D : Model R M) (F : Family (C.sentence D))
    (B : World R) (sat : BackAndForth.Satisfies B.model (C.sentence D)) (size : #B.carrier ≤ ℵ₁) :
    ∃ q : Pointed B, #q.target.carrier ≤ ℵ₁ := by
  classical
  let res := LabelClosed.resolution C sat size
  let i₀ := omegaOneStages.start
  haveI : Nonempty OmegaOne := ⟨i₀⟩
  obtain ⟨p,hp⟩ := F.existsOver (subworld B (res.level i₀)) (res.small i₀) (res.satisfies i₀)
  let start : LocalStage F B sat := ⟨res.level i₀,res.small i₀,res.closed i₀,p,hp⟩
  let good : StageProperty (LocalStage.Arrow (F := F) (B := B) (sat := sat)) (J := OmegaOne) :=
    fun i _ a _ => res.level i ⊆ a.support
  obtain ⟨L,ok⟩ := Transfinite.build LocalStage.Arrow LocalStage.compose start good (by
    intro j L
    haveI : Countable (Iio j) := le_aleph0_iff_set_countable.mp <| lt_aleph_one_iff.mp
      (by simpa only [mk_toType,card_ord] using mk_Iio_lt j (by simp))
    exact LocalStage.next L (res.small j))
  apply LocalStage.finish L (by simp [OmegaOne])
  intro x
  obtain ⟨i,hi⟩ := res.exhaustive x
  exact ⟨i,ok i hi⟩

end KnightModel.RankTwo.Scott.MarkedExtension
