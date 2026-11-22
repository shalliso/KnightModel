import KnightModel.Transfinite.TransferCoordinates

/-! # Back-and-forth for a successor atlas over an arbitrary ordered base -/

namespace KnightModel.Transfinite

open RankTwo Scott Cardinal

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Scott.Model R I} {E : Scott.Model R J} {F : OrderedBF D E}

private theorem base_forward {p : F.State} {n} (r : BaseRelation R n)
    {a : Tuple (BasePoints I) n} {b : Tuple (BasePoints J) n}
    (g : ∀ l, BaseMatch p (a l) (b l)) (h : baseModel D r a) : baseModel E r b := by
  cases r with
  | old r =>
    obtain ⟨s, hs, ha⟩ := h
    have each l := BaseMatch.inl_of ((hs l) ▸ g l)
    choose t eq pair using each
    exact ⟨t,eq,(p.relation r pair).mp ha⟩
  | indexSort =>
    obtain ⟨x,hx⟩ := h
    obtain ⟨y,hy,_⟩ := BaseMatch.inl_of (hx ▸ g 0)
    exact ⟨y,hy⟩
  | vectorSort =>
    obtain ⟨x,hx⟩ := h
    obtain ⟨y,hy,_⟩ := BaseMatch.inr_of (hx ▸ g 0)
    exact ⟨y,hy⟩
  | coefficient v =>
    obtain ⟨u,x,hu,hx,coef⟩ := h
    obtain ⟨w,hw,uw⟩ := BaseMatch.inr_of (hu ▸ g 0)
    obtain ⟨y,hy,xy⟩ := BaseMatch.inl_of (hx ▸ g 1)
    exact ⟨w,y,hw,hy,(uw.coeff xy).symm.trans coef⟩

private theorem graphEq {i : I} {a b : Concrete.Code i} :
    (∀ x y, a.val x = y ↔ b.val x = y) ↔ a = b := by
  constructor
  · intro h
    exact Subtype.ext (DFunLike.ext _ _ fun x => ((h x _).mp rfl).symm)
  · rintro rfl
    exact fun _ _ => Iff.rfl

variable (F) (i : I) (j : J) (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
variable (S : SquareLadders (AtlasIndex κ) κ.ord) (slots : κ.ord.ToType ↪o J)

/-- Every atomic predicate in the actual small and large frame interpretations
agrees at matched parameters and codes. -/
theorem frameInterprets : (frameMatches F i j κ hκ S slots).Interprets
    (smallInterpretation D i) (largeInterpretation E j κ hκ S slots) where
  param_eq := BaseMatch.eq_iff
  code_eq h k := graphEq.symm.trans ((GraphMatch.same h k).trans graphEq)
  base {_ _} r {_ _} h :=
    ⟨base_forward r h,base_forward (F := F.flip) r (fun l => (h l).symm)⟩
  run {p _} k {_ _} h := run_matches p.property k h

/-- The successor back-and-forth retains the old finite position in its support
record, and matches actual frames through the two anchor charts. -/
noncomputable def frameSystem : BackAndForth (smallModel D i) (largeModel E j κ hκ S slots) :=
  (frameMatches F i j κ hκ S slots).system _ _ (frameInterprets F i j κ hκ S slots).atoms

private noncomputable def firstSmall (i : I) : Concrete.SmallFrames i := by
  let w := Word.cons (unitLetter i) Word.root
  let f := throughCode Word.shiftLetter (⟨0,le_rfl⟩ : Letter I) (unitLetter i)
    (zero_lt_unit i) Word.shiftOpenLetter w
  exact ⟨f,(throughCode_top _ _ _ _ _ _ : f.val ⊤ = w) ▸ Word.cons_lt_root _ _⟩

/-- A matching on any old tuple extends to the same tuple in the successor.
The unique named mark is added to its support by one old forth move. -/
theorem frameSystem_old (r : R 1) (lm : ∀ t, D r t ↔ t 0 = i)
    (rm : ∀ t, E r t ↔ t 0 = j) {n} {s : Tuple I n} {t : Tuple J n}
    (ok : F.matchTuples s t) :
    (frameSystem F i j κ hκ S slots).matchTuples
      (fun l => .inl (.inl (s l))) (fun l => .inl (.inl (t l))) := by
  let p : F.State := ⟨n,s,t,ok⟩
  obtain ⟨q,y,qp,pair⟩ := p.extendIndexLeft i
  have pin : y = j := (rm (fun _ => y)).mp ((q.relation r (fun _ => pair)).mp
    ((lm (fun _ => i)).mpr rfl))
  subst y
  have κpos := (aleph0_pos.trans_le hκ).trans_le (Order.le_succ κ)
  let a : AtlasIndex κ := Ordinal.ToType.mk ⟨0, ord_pos.mpr κpos⟩
  refine ⟨{
    state := ⟨q,pair⟩
    left := firstSmall i
    right := largeAnchor j κ S slots a
    a := fun l => .inl (.inl (s l))
    b := fun l => .inl (.inl (t l))
    agree := ?_
    leftRead := fun _ => rfl
    rightRead := fun _ => rfl }⟩
  exact fun l => qp (show (s l,t l) ∈ p.graph from ⟨l,rfl⟩)

end KnightModel.Transfinite
