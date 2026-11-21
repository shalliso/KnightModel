import KnightModel.RankTwo.AtlasSuccessor
import KnightModel.RankTwo.WalkCovariant

/-! # Finite coordinate transitions on the full thickened line

A rule records only words, and is a span of two injective word operations.
The interval guards likewise use words. Thus none of the index ordinals
becomes a parameter of the transition description. -/

namespace KnightModel.RankTwo

open Set

inductive CoordinateRule (A : Type*) where
  | first (u v : Word A)
  | interval (l u l' u' : Word A)
  | tail (source target : TailShape A)

structure GuardedRule (A : Type*) where
  lower : Option (Word A)
  upper : Word A
  rule : CoordinateRule A

namespace GuardedRule

def contains {A : Type*} [LinearOrder A] (r : GuardedRule A) (w : Word A) : Prop :=
  (∀ lo ∈ r.lower, lo < w) ∧ w ≤ r.upper

end GuardedRule

namespace CoordinateRule

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- Both coordinates are obtained from a common local word or interval parameter. -/
def Rel : CoordinateRule A → Word A → Word A → Prop
  | .first u v, x, y => ∃ z, x = Word.through shift u z ∧ y = Word.through shift v z
  | .interval l u l' u', x, y => ∃ h : l < u, ∃ h' : l' < u', ∃ z : Ioi (Word.cons o Word.root),
      x = (Word.H shift o d hd upper l u h z).val ∧ y = (Word.H shift o d hd upper l' u' h' z).val
  | .tail s t, x, y => ∃ z, x = s.apply shift z ∧ y = t.apply shift z

theorem functional (r : CoordinateRule A) {x y z : Word A}
    (h : r.Rel shift o d hd upper x y) (k : r.Rel shift o d hd upper x z) : y = z := by
  cases r with
  | first u v =>
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨b, hb, rfl⟩ := k
    exact congrArg _ ((Word.strictMono_through shift u).injective (ha.symm.trans hb))
  | interval l u l' u' =>
    obtain ⟨hu, hu', a, ha, rfl⟩ := h
    obtain ⟨_, _, b, hb, rfl⟩ := k
    exact congrArg (fun w => (Word.H shift o d hd upper l' u' hu' w).val)
      ((Word.H shift o d hd upper l u hu).injective (Subtype.ext (ha.symm.trans hb)))
  | tail s t =>
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨b, hb, rfl⟩ := k
    exact congrArg _ ((s.embedding shift).injective (ha.symm.trans hb))

end CoordinateRule

namespace CoherentLadders

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

/-- On an interior sector whose preceding marks lie inside the copied tail,
the entire enclosing map is the same prefix with its endpoint fold. -/
theorem transport_interior_shape {n m g i b : J} (hng : n < m) (hmg : m < g)
    (hgi : g < i) (hib : i ≤ b) {s : TailShape A} (fits : C.Fits b i s)
    (copy : ∀ k, n < k → k < i → C.word b k = s.prefix ++ C.word i k)
    (w : C.markedRows.sector g g) :
    (C.transports shift o d hd upper (hgi.le.trans hib) w).val =
      s.apply shift (C.transports shift o d hd upper hgi.le w).val := by
  rw [C.shape_apply_of_le_mark shift fits hgi _ (C.transports shift o d hd upper hgi.le w).property.1]
  by_cases prev : ∃ p < g, ∀ j < g, j ≤ p
  · obtain ⟨p, hpg, hp⟩ := prev
    exact C.transports_succ_prepend shift o d hd upper hpg _ _ hp _
      (copy p (hng.trans_le (hp m hmg)) (hpg.trans hgi)) (copy g (hng.trans hmg) hgi) w
  · exact C.transports_limit_prepend shift o d hd upper _ _ (hng.trans hmg)
      (interior_of_no_previous prev) (fun j hnj hjg => copy j hnj (hjg.trans_lt hgi)) w

/-- A single word-only rule works on a whole final interval below a limit,
including all points of the limit sector itself. -/
theorem limit_rule {i b c : J} (hib : i ≤ b) (hic : i ≤ c) (pos : ∃ j, j < i)
    (lim : ∀ n < i, ∃ x, n < x ∧ x < i) :
    ∃ m < i, ∃ r : CoordinateRule A, ∀ g, m < g → (hgi : g ≤ i) →
      ∀ w : C.markedRows.sector g g,
        r.Rel shift o d hd upper
          (C.transports shift o d hd upper (hgi.trans hib) w).val
          (C.transports shift o d hd upper (hgi.trans hic) w).val := by
  let s := C.shape hib pos
  let t := C.shape hic pos
  have hs : C.Fits b i s := C.shape_fits _ _
  have ht : C.Fits c i t := C.shape_fits _ _
  obtain ⟨n, hn, hns⟩ := hs.1
  obtain ⟨k, hk, hkt⟩ := ht.1
  obtain ⟨m, hmm, hmi⟩ := lim (max n k) (max_lt hn hk)
  refine ⟨m, hmi, .tail s t, ?_⟩
  intro g hmg hgi w
  rcases hgi.lt_or_eq with hgi | rfl
  · exact ⟨_, C.transport_interior_shape shift o d hd upper
      ((le_max_left _ _).trans_lt hmm) hmg hgi hib hs hns w,
      C.transport_interior_shape shift o d hd upper
      ((le_max_right _ _).trans_lt hmm) hmg hgi hic ht hkt w⟩
  · exact ⟨w.val, C.transports_limit_apply shift o d hd upper hib pos lim w,
      C.transports_limit_apply shift o d hd upper hic pos lim w⟩

private theorem transport_le_mark_iff {g b k : J} (hgb : g ≤ b) (hkb : k ≤ b)
    (w : C.markedRows.sector g g) :
    (C.transports shift o d hd upper hgb w).val ≤ C.mark b k ↔ g ≤ k := by
  let z := C.transports shift o d hd upper hgb w
  constructor
  · intro hz
    exact le_of_not_gt (fun h => (not_le_of_gt (z.property.2 k h)) hz)
  · intro hgk
    exact z.property.1.trans ((C.mark_strictMonoOn b).monotoneOn hgb hkb hgk)

private theorem transport_first {g b : J} (hgb : g ≤ b) (hn : ¬∃ i, i < g)
    (w : C.markedRows.sector g g) :
    (C.transports shift o d hd upper hgb w).val = Word.through shift (C.mark b g) w.val := by
  classical
  unfold transports
  rw [dif_neg hn]
  rfl

/-- A finite list describes the change on each closed initial interval. Its
guards and operations use only words and letters and hence no ordinal parameters. -/
theorem finite_guarded_rules (b c i : J) (hib : i ≤ b) (hic : i ≤ c) :
    ∃ rs : List (GuardedRule A), ∀ g (hgb : g ≤ b) (hgc : g ≤ c)
      (w : C.markedRows.sector g g),
      (g ≤ i ↔ ∃ r ∈ rs, r.contains (C.transports shift o d hd upper hgb w).val) ∧
      ∀ r ∈ rs, r.contains (C.transports shift o d hd upper hgb w).val →
        r.rule.Rel shift o d hd upper (C.transports shift o d hd upper hgb w).val
          (C.transports shift o d hd upper hgc w).val := by
  classical
  induction i using wellFounded_lt.induction with
  | h i ih =>
    by_cases pos : ∃ j, j < i
    · have last : ∃ m < i, ∃ r : CoordinateRule A, ∀ g, m < g → (hgi : g ≤ i) →
          ∀ w : C.markedRows.sector g g,
            r.Rel shift o d hd upper
              (C.transports shift o d hd upper (hgi.trans hib) w).val
              (C.transports shift o d hd upper (hgi.trans hic) w).val := by
        by_cases prev : ∃ p < i, ∀ j < i, j ≤ p
        · obtain ⟨p, hpi, prev⟩ := prev
          refine ⟨p, hpi, .interval (C.mark b p) (C.mark b i) (C.mark c p) (C.mark c i), ?_⟩
          intro g hpg hgi w
          obtain rfl : g = i := hgi.eq_of_not_lt (fun h => (not_le_of_gt hpg) (prev g h))
          exact ⟨_, _, _, C.transports_succ_apply shift o d hd upper hpi hib prev w,
            C.transports_succ_apply shift o d hd upper hpi hic prev w⟩
        · exact C.limit_rule shift o d hd upper hib hic pos (interior_of_no_previous prev)
      obtain ⟨m, hmi, r, hlast⟩ := last
      obtain ⟨rs, hrs⟩ := ih m hmi (hmi.le.trans hib) (hmi.le.trans hic)
      let lastRule : GuardedRule A := ⟨some (C.mark b m), C.mark b i, r⟩
      refine ⟨lastRule :: rs, ?_⟩
      intro g hgb hgc w
      obtain ⟨cover, valid⟩ := hrs g hgb hgc w
      have guard : lastRule.contains (C.transports shift o d hd upper hgb w).val ↔ m < g ∧ g ≤ i := by
        simp only [lastRule, GuardedRule.contains, Option.mem_some_iff, forall_eq]
        rw [C.transport_le_mark_iff shift o d hd upper hgb hib]
        rw [← not_le, C.transport_le_mark_iff shift o d hd upper hgb (hmi.le.trans hib), not_le]
      constructor
      · constructor
        · intro hgi
          rcases le_or_gt g m with hgm | hmg
          · obtain ⟨rr, hrr, hg⟩ := cover.mp hgm
            exact ⟨rr, List.mem_cons_of_mem _ hrr, hg⟩
          · exact ⟨lastRule, List.mem_cons_self, guard.mpr ⟨hmg, hgi⟩⟩
        · rintro ⟨rr, hrr, hg⟩
          rcases List.mem_cons.mp hrr with rfl | hrr
          · exact (guard.mp hg).2
          · exact (cover.mpr ⟨rr,hrr,hg⟩).trans hmi.le
      · intro rr hrr hg
        rcases List.mem_cons.mp hrr with rfl | hrr
        · exact hlast g (guard.mp hg).1 (guard.mp hg).2 w
        · exact valid _ hrr hg
    · let start : GuardedRule A := ⟨none, C.mark b i, .first (C.mark b i) (C.mark c i)⟩
      refine ⟨[start], ?_⟩
      intro g hgb hgc w
      have guard : start.contains (C.transports shift o d hd upper hgb w).val ↔ g ≤ i := by
        simpa [start, GuardedRule.contains] using C.transport_le_mark_iff shift o d hd upper hgb hib w
      constructor
      · simp [guard]
      · intro r hr hrw
        obtain rfl : r = start := List.mem_singleton.mp hr
        have he := (guard.mp hrw).eq_of_not_lt (fun h => pos ⟨g,h⟩)
        subst g
        exact ⟨_, C.transport_first shift o d hd upper hib pos w,
          C.transport_first shift o d hd upper hic pos w⟩

/-- The graph of the actual coordinate change is exactly a finite union of the
guarded word-operation spans; in particular these describe its inverse as well. -/
theorem change_graph {a b : J} (hab : a ≤ b) :
    ∃ rs : List (GuardedRule A), ∀ x y : Word A,
      C.markedRows.change (C.transports shift o d hd upper) hab x = y ↔
      ∃ r ∈ rs, r.contains x ∧ r.rule.Rel shift o d hd upper x y := by
  let q := C.transports shift o d hd upper
  obtain ⟨rs, hrs⟩ := C.finite_guarded_rules shift o d hd upper a b a le_rfl hab
  refine ⟨rs, ?_⟩
  intro x y
  obtain ⟨z, rfl⟩ := (C.markedRows.chart q a).surjective x
  let g := C.markedRows.index z.val
  let w : C.markedRows.sector g g := ⟨C.markedRows.word z.val, z.val.property⟩
  have hga : g ≤ a := C.markedRows.le_anchor_iff.mp z.property
  obtain ⟨cover, valid⟩ := hrs g hga (hga.trans hab) w
  rw [C.markedRows.change_chart]
  constructor
  · intro he
    subst y
    obtain ⟨r, hr, hg⟩ := cover.mp hga
    exact ⟨r, hr, hg, valid r hr hg⟩
  · rintro ⟨r, hr, hg, hy⟩
    exact r.rule.functional shift o d hd upper (valid r hr hg) hy

end CoherentLadders
end KnightModel.RankTwo
