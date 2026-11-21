import KnightModel.RankTwo.RestrictionTree

/-! # Specializing the narrow restriction tree

On each fixed-color preorder, the ordinal height of the earlier predecessors
strictly increases along any forward comparison. Points with the same height
therefore all lie below the first point of their color and height. A second
ordinal rank distinguishes the points in each such countable set.
-/

namespace KnightModel.RankTwo.Restriction

open Cardinal Ordinal Set

/-- The comparison relations of the rows are transitive within each fiber. -/
def TransitiveRows (rows : OmegaTwo → Chart OmegaTwo) : Prop :=
  ∀ b x y z, x < b → y < b → z < b → (rows b).color x = (rows b).color y →
    (rows b).color y = (rows b).color z → (rows b).rel x y →
    (rows b).rel y z → (rows b).rel x z

private def earlierCone (C : Chart OmegaTwo) (x : OmegaTwo) : Set OmegaTwo :=
  {y | y < x ∧ C.color y = C.color x ∧ C.rel y x}

private def height (C : Chart OmegaTwo) (x : OmegaTwo) : Ordinal.{0} :=
  typeLT (earlierCone C x)

private def sameHeight (C : Chart OmegaTwo) (x : OmegaTwo) : Set OmegaTwo :=
  {y | y < x ∧ C.color y = C.color x ∧ height C y = height C x}

private def secondHeight (C : Chart OmegaTwo) (x : OmegaTwo) : Ordinal.{0} :=
  typeLT (sameHeight C x)

/-- An embedding of a set into a proper principal initial segment proves a
strict comparison of order types. -/
private theorem typeLT_lt_at {s t : Set OmegaTwo} {x : OmegaTwo}
    (hx : x ∈ t) (h : ∀ y ∈ s, y ∈ t ∧ y < x) : typeLT s < typeLT t := by
  let p : t := ⟨x, hx⟩
  let f (y : s) : Iio p := ⟨⟨y.val, (h y.val y.property).1⟩, (h y.val y.property).2⟩
  have he : typeLT s ≤ typeLT (Iio p) :=
    (RelEmbedding.ofMonotone f (fun _ _ hxy => hxy)).ordinal_type_le
  exact he.trans_lt (typein_lt_type (· < ·) p)

private theorem height_increases {rows : OmegaTwo → Chart OmegaTwo}
    (trans : TransitiveRows rows) {b x y : OmegaTwo} (hxy : x < y) (hyb : y < b)
    (hc : (rows b).color x = (rows b).color y) (hr : (rows b).rel x y) :
    height (rows b) x < height (rows b) y := by
  apply typeLT_lt_at (x := x) ⟨hxy, hc, hr⟩
  rintro z ⟨hzx, hcol, hrel⟩
  exact ⟨⟨hzx.trans hxy, hcol.trans hc, trans b z x y (hzx.trans (hxy.trans hyb))
    (hxy.trans hyb) hyb hcol hc hrel hr⟩, hzx⟩

private theorem first_small {rows : OmegaTwo → Chart OmegaTwo} (H : LocalCharts rows)
    {b x : OmegaTwo} (hx : x < b) : (earlierCone (rows b) x).Countable := by
  apply (H.small b x hx).mono
  rintro y ⟨hy, hcol, hrel⟩
  exact ⟨hy.trans hx, hcol, hrel⟩

private theorem second_small {rows : OmegaTwo → Chart OmegaTwo} (H : LocalCharts rows)
    (trans : TransitiveRows rows) {b x : OmegaTwo} (hx : x < b) :
    (sameHeight (rows b) x).Countable := by
  let s := sameHeight (rows b) x
  by_cases hs : s.Nonempty
  · let m := wellFounded_lt.min s hs
    obtain ⟨hmx, hmc, hmh⟩ := (show m ∈ sameHeight (rows b) x from wellFounded_lt.min_mem s hs)
    apply (H.small b m (hmx.trans hx)).mono
    intro y hy
    obtain ⟨hyx, hyc, hyh⟩ := hy
    have c := hyc.trans hmc.symm
    have hmy : m ≤ y := wellFounded_lt.min_le (s := s) ⟨hyx, hyc, hyh⟩
    obtain ry | rm := H.compare b y m (hyx.trans hx) (hmx.trans hx) c
    · exact ⟨hyx.trans hx, c, ry⟩
    · rcases hmy.eq_or_lt with e | e
      · subst y
        exact ⟨hmx.trans hx, rfl, rm⟩
      · exact False.elim ((height_increases trans e (hyx.trans hx) c.symm rm).ne
          (hmh.trans hyh.symm))
  · change s.Countable
    rw [Set.not_nonempty_iff_eq_empty.mp hs]
    exact countable_empty

private theorem countableType {s : Set OmegaTwo} (hs : s.Countable) :
    typeLT s < (aleph.{0} 1).ord := by
  rw [lt_ord, card_type]
  exact lt_aleph_one_iff.mpr (le_aleph0_iff_set_countable.mpr hs)

private theorem second_increases {C : Chart OmegaTwo} {x y : OmegaTwo}
    (hxy : x < y) (hc : C.color x = C.color y) (hh : height C x = height C y) :
    secondHeight C x < secondHeight C y := by
  apply typeLT_lt_at (x := x) ⟨hxy, hc, hh⟩
  rintro z ⟨hzx, hcz, hhz⟩
  exact ⟨⟨hzx.trans hxy, hcz.trans hc, hhz.trans hh⟩, hzx⟩

/-- Agreement on the closed prefix up through the terminal index. -/
structure AgreeThrough (C D : Chart OmegaTwo) (x : OmegaTwo) : Prop where
  color : ∀ y ≤ x, C.color y = D.color y
  rel : ∀ y ≤ x, ∀ z ≤ x, C.rel y z ↔ D.rel y z

private theorem congr_height {C D : Chart OmegaTwo} {x y : OmegaTwo}
    (h : AgreeThrough C D x) (hy : y ≤ x) : height C y = height D y := by
  have he : earlierCone C y = earlierCone D y := by
    ext z
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    by_cases hz : z < y
    · rw [h.color z (hz.le.trans hy), h.color y hy, h.rel z (hz.le.trans hy) y hy]
    · simp [hz]
  exact congrArg (fun s : Set OmegaTwo => typeLT s) he

private theorem congr_second {C D : Chart OmegaTwo} {x : OmegaTwo}
    (h : AgreeThrough C D x) : secondHeight C x = secondHeight D x := by
  have he : sameHeight C x = sameHeight D x := by
    ext z
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    by_cases hz : z < x
    · rw [h.color z hz.le, h.color x le_rfl, congr_height h hz.le, congr_height h le_rfl]
    · simp [hz]
  exact congrArg (fun s : Set OmegaTwo => typeLT s) he

/-- A named representative of a closed prefix of one endpoint's chart. -/
structure ClosedPrefix where
  last : OmegaTwo
  endpoint : OmegaTwo
  before : last < endpoint

/-- Label by two countable ordinals and the color of the last coordinate. -/
noncomputable def ClosedPrefix.label {rows : OmegaTwo → Chart OmegaTwo}
    (p : ClosedPrefix) (H : LocalCharts rows) (trans : TransitiveRows rows) :
    ℕ × OmegaOne × OmegaOne :=
  ((rows p.endpoint).color p.last,
    ToType.mk ⟨height (rows p.endpoint) p.last, countableType (first_small H p.before)⟩,
    ToType.mk ⟨secondHeight (rows p.endpoint) p.last,
      countableType (second_small H trans p.before)⟩)

private def ordinalAt (v : OmegaOne) : Ordinal.{0} := v.toOrd.val

private theorem ordinalAt_mk (v : Set.Iio (aleph.{0} 1).ord) :
    ordinalAt (ToType.mk v) = v.val := congrArg Subtype.val (ToType.mk.symm_apply_apply v)

/-- Changing the row representative of a single tree node preserves its label. -/
theorem label_agrees {rows : OmegaTwo → Chart OmegaTwo}
    (H : LocalCharts rows) (trans : TransitiveRows rows) (p q : ClosedPrefix)
    (last : p.last = q.last) (h : AgreeThrough (rows p.endpoint) (rows q.endpoint) p.last) :
    p.label H trans = q.label H trans := by
  apply Prod.ext (h.color _ le_rfl |>.trans (congrArg (rows q.endpoint).color last))
  apply Prod.ext
  · apply congrArg ToType.mk
    apply Subtype.ext
    exact (congr_height h le_rfl).trans (congrArg (height (rows q.endpoint)) last)
  · apply congrArg ToType.mk
    apply Subtype.ext
    exact (congr_second h).trans (congrArg (secondHeight (rows q.endpoint)) last)

/-- Comparable distinct closed-prefix nodes receive different labels.
Together with `label_agrees`, this specializes the restriction tree after
identifying the different representatives of each closed prefix. -/
theorem label_separates {rows : OmegaTwo → Chart OmegaTwo}
    (H : LocalCharts rows) (trans : TransitiveRows rows) (p q : ClosedPrefix)
    (last : p.last < q.last) (h : AgreeThrough (rows p.endpoint) (rows q.endpoint) p.last) :
    p.label H trans ≠ q.label H trans := by
  intro eq
  have col := congrArg Prod.fst eq
  have e₁ := congrArg (fun v : ℕ × OmegaOne × OmegaOne => ordinalAt v.2.1) eq
  have e₂ := congrArg (fun v : ℕ × OmegaOne × OmegaOne => ordinalAt v.2.2) eq
  simp only [ClosedPrefix.label, ordinalAt_mk] at col e₁ e₂
  have hc := (h.color _ le_rfl).symm.trans col
  have hh := (congr_height h le_rfl).symm.trans e₁
  exact (second_increases last hc hh).ne ((congr_second h).symm.trans e₂)

/-- Exactly ℵ₁ labels are available. -/
theorem cardinal_specializing_labels : #(ℕ × OmegaOne × OmegaOne) = ℵ₁ := by
  simp only [mk_prod, mk_nat, mk_toType, card_ord, mul_eq_self (aleph0_le_aleph 1)]
  exact aleph0_mul_eq (aleph0_le_aleph 1)

end KnightModel.RankTwo.Restriction
