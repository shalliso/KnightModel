import Mathlib.Data.Prod.Lex
import Mathlib.Order.Hom.Basic
import Mathlib.Order.WellFounded

/-! # The outer line of a marked atlas

A row marks a copy of the index interval through its endpoint in a common word
order. The outer line is the lexicographic sum of the native sectors (one
from each row). Isomorphisms between corresponding sectors glue to charts on
the actual initial segments of the outer line. -/

namespace KnightModel.RankTwo

/-- Only entries `mark b a` with `a ≤ b` are used. -/
structure MarkedRows (J W : Type*) [LinearOrder J] [LinearOrder W] [OrderTop W] where
  mark : J → J → W
  mark_self : ∀ b, mark b b = ⊤
  mark_strictMonoOn : ∀ b, StrictMonoOn (mark b) (Set.Iic b)

namespace MarkedRows

variable {J W : Type*} [LinearOrder J] [LinearOrder W] [OrderTop W]
variable (D : MarkedRows J W)

/-- The points of row `b` whose first weakly larger mark is indexed by `a`. -/
def sector (b a : J) : Set W :=
  {w | w ≤ D.mark b a ∧ ∀ i < a, D.mark b i < w}

theorem mark_mem_sector {a b : J} (hab : a ≤ b) : D.mark b a ∈ D.sector b a :=
  ⟨le_rfl, fun i hi => D.mark_strictMonoOn b (hi.le.trans hab) hab hi⟩

theorem sector_lt_sector {b a c : J} (hac : a < c)
    {x y : W} (hx : x ∈ D.sector b a) (hy : y ∈ D.sector b c) : x < y :=
  hx.1.trans_lt (hy.2 a hac)

theorem sector_index_unique {a c b : J} {w : W}
    (ha : w ∈ D.sector b a) (hc : w ∈ D.sector b c) : a = c := by
  rcases lt_trichotomy a c with h | h | h
  · exact False.elim (lt_irrefl w (D.sector_lt_sector h ha hc))
  · exact h
  · exact False.elim (lt_irrefl w (D.sector_lt_sector h hc ha))

theorem exists_sector [WellFoundedLT J] (b : J) (w : W) :
    ∃ a ≤ b, w ∈ D.sector b a := by
  let candidates : Set J := {i | i ≤ b ∧ w ≤ D.mark b i}
  have hb : b ∈ candidates := ⟨le_rfl, by rw [D.mark_self]; exact le_top⟩
  obtain ⟨a, ha, hmin⟩ := wellFounded_lt.has_min candidates ⟨b, hb⟩
  refine ⟨a, ha.1, ha.2, ?_⟩
  intro i hi
  exact lt_of_not_ge (fun h => hmin i ⟨hi.le.trans ha.1, h⟩ hi)

/-- The lexicographic sum of native sectors. -/
abbrev Outer := {p : J ×ₗ W // (ofLex p).2 ∈ D.sector (ofLex p).1 (ofLex p).1}

def index (x : D.Outer) : J := (ofLex x.val).1

def word (x : D.Outer) : W := (ofLex x.val).2

def point (a : J) (w : D.sector a a) : D.Outer := ⟨toLex (a, w.val), w.property⟩

/-- The final point of the native sector at index `a`. -/
def anchor (a : J) : D.Outer := D.point a ⟨D.mark a a, D.mark_mem_sector le_rfl⟩

@[simp] theorem index_anchor (a : J) : D.index (D.anchor a) = a := rfl

theorem anchor_strictMono : StrictMono D.anchor := by
  intro a b hab
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

theorem le_anchor_iff {x : D.Outer} {b : J} : x ≤ D.anchor b ↔ D.index x ≤ b := by
  constructor
  · exact fun h => Prod.Lex.monotone_fst _ _ h
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact Prod.Lex.le_iff.mpr (Or.inl hlt)
    · refine Prod.Lex.le_iff.mpr (Or.inr ⟨heq, ?_⟩)
      change D.word x ≤ D.mark b b
      rw [D.mark_self]
      exact le_top

/-- A transport is local data between two explicitly defined subsets of the word order. -/
abbrev Transports := ∀ {a b : J}, a ≤ b → D.sector a a ≃o D.sector b a

variable (q : D.Transports)

/-- Glue the sector maps at a fixed endpoint. -/
def chartValue (b : J) (x : Set.Iic (D.anchor b)) : W :=
  (q (D.le_anchor_iff.mp x.property) ⟨D.word x.val, x.val.property⟩).val

theorem chartValue_mem_sector (b : J) (x : Set.Iic (D.anchor b)) :
    D.chartValue q b x ∈ D.sector b (D.index x.val) :=
  (q (D.le_anchor_iff.mp x.property) ⟨D.word x.val, x.val.property⟩).property

theorem chartValue_strictMono (b : J) : StrictMono (D.chartValue q b) := by
  rintro ⟨⟨⟨a, u⟩, hu⟩, hau⟩ ⟨⟨⟨c, v⟩, hv⟩, hcv⟩ hlt
  obtain ha | ⟨hac, huv⟩ := Prod.Lex.toLex_lt_toLex.mp hlt
  · exact D.sector_lt_sector ha (D.chartValue_mem_sector q b _) (D.chartValue_mem_sector q b _)
  · change a = c at hac
    subst c
    have hab := D.le_anchor_iff.mp hau
    exact (q hab).strictMono (show (⟨u, hu⟩ : D.sector a a) < ⟨v, hv⟩ from huv)

theorem chartValue_surjective [WellFoundedLT J] (b : J) :
    Function.Surjective (D.chartValue q b) := by
  intro w
  obtain ⟨a, hab, hw⟩ := D.exists_sector b w
  let v := (q hab).symm ⟨w, hw⟩
  refine ⟨⟨D.point a v, D.le_anchor_iff.mpr hab⟩, ?_⟩
  exact congrArg Subtype.val ((q hab).apply_symm_apply ⟨w, hw⟩)

/-- The sector-by-sector isomorphism from a genuine principal segment onto all words. -/
noncomputable def chart [WellFoundedLT J] (b : J) : Set.Iic (D.anchor b) ≃o W :=
  StrictMono.orderIsoOfRightInverse _ (D.chartValue_strictMono q b)
    (fun w => (D.chartValue_surjective q b w).choose)
    (fun w => (D.chartValue_surjective q b w).choose_spec)

@[simp] theorem chart_apply [WellFoundedLT J] (b : J) (x : Set.Iic (D.anchor b)) :
    D.chart q b x = D.chartValue q b x := rfl

/-- Each sector transport takes its final point to the corresponding mark. -/
theorem chart_anchor [WellFoundedLT J] {a b : J} (hab : a ≤ b) :
    D.chart q b ⟨D.anchor a, D.le_anchor_iff.mpr hab⟩ = D.mark b a := by
  apply le_antisymm (D.chartValue_mem_sector q b _).1
  let z : D.sector b a := ⟨D.mark b a, D.mark_mem_sector hab⟩
  have h : (q hab).symm z ≤ (⟨D.mark a a, D.mark_mem_sector le_rfl⟩ : D.sector a a) :=
    ((q hab).symm z).property.1
  exact show (z.val : W) ≤ _ from (q hab).symm_apply_le.mp h

end MarkedRows
end KnightModel.RankTwo
