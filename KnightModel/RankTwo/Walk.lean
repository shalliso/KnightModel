import Mathlib.Order.WellFounded

/-!
# Minimal walks on coherently labelled ladders

The labels of a square ladder are the positions on that ladder, transported by
a fixed increasing sequence into the word alphabet.  The proofs here use only
the intrinsic order and coherence of these labels.  The index order need not
have a greatest element.
-/

namespace KnightModel.RankTwo

universe u v

/-- Every tail below `d` has a ladder member strictly below `d`. -/
def LadderLimit {J : Type u} [LT J] (c : Set J) (d : J) : Prop :=
  ∀ n < d, ∃ t ∈ c, n < t ∧ t < d

/-- Closed cofinal ladders, with increasing labels that agree on coherent
initial segments.  Successor ladders may be singletons.  No closure condition
is imposed at the bottom point. -/
structure CoherentLadders (J : Type u) (A : Type v) [LinearOrder J] [LinearOrder A] where
  ladder : J → Set J
  below : ∀ {b x}, x ∈ ladder b → x < b
  cofinal : ∀ {g b}, g < b → ∃ x ∈ ladder b, g ≤ x
  label : (b : J) → ladder b → A
  label_strictMono : ∀ b, StrictMono (label b)
  closed : ∀ {b d}, d < b → (∃ n, n < d) → LadderLimit (ladder b) d → d ∈ ladder b
  coherent : ∀ {b d}, d < b → (∃ n, n < d) → LadderLimit (ladder b) d →
    ∀ {x}, x < d → (x ∈ ladder b ↔ x ∈ ladder d)
  label_coherent : ∀ {b d}, d < b → (∃ n, n < d) → LadderLimit (ladder b) d →
    ∀ {x} (_ : x < d) (hb : x ∈ ladder b) (hd : x ∈ ladder d),
      label b ⟨x, hb⟩ = label d ⟨x, hd⟩

namespace CoherentLadders

variable {J : Type u} {A : Type v} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)

/-- The next stop is the least ladder point at least the target. -/
noncomputable def next (b g : J) (h : g < b) : J :=
  wellFounded_lt.min {x | x ∈ C.ladder b ∧ g ≤ x} (C.cofinal h)

theorem next_mem {b g : J} (h : g < b) : C.next b g h ∈ C.ladder b :=
  (wellFounded_lt.min_mem {x | x ∈ C.ladder b ∧ g ≤ x} (C.cofinal h)).1

theorem le_next {b g : J} (h : g < b) : g ≤ C.next b g h :=
  (wellFounded_lt.min_mem {x | x ∈ C.ladder b ∧ g ≤ x} (C.cofinal h)).2

theorem next_lt {b g : J} (h : g < b) : C.next b g h < b :=
  C.below (C.next_mem h)

theorem next_le {b g x : J} (h : g < b) (hx : x ∈ C.ladder b) (hgx : g ≤ x) :
    C.next b g h ≤ x := by
  apply le_of_not_gt
  exact wellFounded_lt.not_lt_min {z | z ∈ C.ladder b ∧ g ≤ z} ⟨hx, hgx⟩

theorem next_mono {b g d : J} (hd : d < b) (hgd : g ≤ d) :
    C.next b g (lt_of_le_of_lt hgd hd) ≤ C.next b d hd :=
  C.next_le _ (C.next_mem hd) (hgd.trans (C.le_next hd))

/-- First letter of a nonempty walk. -/
noncomputable def slot (b g : J) (h : g < b) : A :=
  C.label b ⟨C.next b g h, C.next_mem h⟩

local instance : WellFoundedRelation J := ⟨(· < ·), wellFounded_lt⟩

/-- `word b g` records a minimal walk from `b` down to `g`. The empty word
also totalizes the definition at targets above its domain. -/
noncomputable def word (b g : J) : List A :=
  if h : g < b then C.slot b g h :: word (C.next b g h) g else []
termination_by b
decreasing_by exact C.next_lt _

theorem word_of_lt {b g : J} (h : g < b) :
    C.word b g = C.slot b g h :: C.word (C.next b g h) g := by
  rw [word]
  exact dif_pos h

@[simp] theorem word_of_le {b g : J} (h : b ≤ g) : C.word b g = [] := by
  rw [word]
  exact dif_neg (not_lt.mpr h)

/-- The label at a fixed target is locally constant from below unless that
target is a ladder limit point. In the constant case the next stop is already
the same, which is stronger than equality of slots. -/
theorem next_constant_below {b d : J} (hdb : d < b) (h : ¬LadderLimit (C.ladder b) d) :
    ∃ n < d, ∀ x, n < x → (hxd : x < d) →
      C.next b x (hxd.trans hdb) = C.next b d hdb := by
  classical
  unfold LadderLimit at h
  push Not at h
  obtain ⟨n, hnd, hn⟩ := h
  refine ⟨n, hnd, ?_⟩
  intro x hnx hxd
  apply le_antisymm (C.next_mono hdb hxd.le)
  apply C.next_le hdb (C.next_mem (hxd.trans hdb))
  exact hn _ (C.next_mem (hxd.trans hdb)) (hnx.trans_le (C.le_next (hxd.trans hdb)))

/-- At a ladder limit, walks to smaller targets take their first step already
inside the coherent restriction. -/
theorem next_at_limit {b d x : J} (hdb : d < b) (hx : x < d)
    (hlim : LadderLimit (C.ladder b) d) :
    C.next b x (hx.trans hdb) = C.next d x hx := by
  obtain ⟨t, ht, hxt, htd⟩ := hlim x hx
  have hsmall := (C.next_le (hx.trans hdb) ht hxt.le).trans_lt htd
  apply le_antisymm
  · exact C.next_le _ ((C.coherent hdb ⟨x, hx⟩ hlim (C.next_lt hx)).mpr (C.next_mem hx)) (C.le_next hx)
  · exact C.next_le _ ((C.coherent hdb ⟨x, hx⟩ hlim hsmall).mp (C.next_mem _)) (C.le_next _)

theorem word_at_limit {b d x : J} (hdb : d < b) (hx : x < d)
    (hlim : LadderLimit (C.ladder b) d) : C.word b x = C.word d x := by
  have he := C.next_at_limit hdb hx hlim
  have hs : C.slot b x (hx.trans hdb) = C.slot d x hx := by
    unfold slot
    have hsmall : C.next b x (hx.trans hdb) < d := he ▸ C.next_lt hx
    have hb := C.next_mem (hx.trans hdb)
    have hd := (C.coherent hdb ⟨x, hx⟩ hlim hsmall).mp hb
    exact (C.label_coherent hdb ⟨x, hx⟩ hlim hsmall hb hd).trans
      (congrArg (C.label d) (Subtype.ext he))
  rw [C.word_of_lt (hx.trans hdb), C.word_of_lt hx, hs, he]

/-- The tail factorization, including the last slot precisely when needed.
The exceptional slot strictly exceeds every first letter of the lower chart.
The weak hypothesis on `d` also allows successors, whose strict tail may be empty. -/
theorem tail {b d : J} (hdb : d ≤ b) (hpos : ∃ n, n < d) :
    ∃ s : List A,
      (∃ n < d, ∀ x, n < x → x < d → C.word b x = s ++ C.word d x) ∧
      (C.word b d = s ∨ ∃ a, C.word b d = s ++ [a] ∧
        ∀ x (hx : x < d), C.slot d x hx < a) := by
  classical
  induction b using (wellFounded_lt (α := J)).induction with
  | h b ih =>
    obtain he | hbd := eq_or_lt_of_le hdb
    · subst b
      obtain ⟨n, hn⟩ := hpos
      exact ⟨[], ⟨n, hn, by simp⟩, Or.inl (C.word_of_le le_rfl)⟩
    by_cases ha : LadderLimit (C.ladder b) d
    · obtain ⟨n, hn⟩ := hpos
      have hd := C.closed hbd ⟨n, hn⟩ ha
      have hnext := le_antisymm (C.next_le hbd hd le_rfl) (C.le_next hbd)
      refine ⟨[], ⟨n, hn, fun x _ hx => by simpa using C.word_at_limit hbd hx ha⟩,
        Or.inr ⟨C.slot b d hbd, ?_, ?_⟩⟩
      · rw [C.word_of_lt hbd, hnext, C.word_of_le le_rfl]
        rfl
      · intro x hx
        have hm := C.next_mem hx
        have hs := C.next_lt hx
        have hb := (C.coherent hbd ⟨n, hn⟩ ha hs).mpr hm
        change C.label d _ < C.label b _
        rw [← C.label_coherent hbd ⟨n, hn⟩ ha hs hb hm]
        apply C.label_strictMono
        change C.next d x hx < C.next b d hbd
        rwa [hnext]
    · obtain ⟨n, hn, hnxt⟩ := C.next_constant_below hbd ha
      obtain ⟨s, ⟨m, hm, htail⟩, hend⟩ := ih (C.next b d hbd) (C.next_lt hbd) (C.le_next hbd)
      refine ⟨C.slot b d hbd :: s, ⟨max m n, max_lt hm hn, ?_⟩, ?_⟩
      · intro x hmx hx
        have he := hnxt x (lt_of_le_of_lt (le_max_right _ _) hmx) hx
        have hs : C.slot b x (hx.trans hbd) = C.slot b d hbd :=
          congrArg (C.label b) (Subtype.ext he)
        rw [C.word_of_lt (hx.trans hbd), hs, he, htail x (lt_of_le_of_lt (le_max_left _ _) hmx) hx]
        rfl
      · rw [C.word_of_lt hbd]
        rcases hend with h | ⟨a, h, ha⟩
        · exact Or.inl (congrArg _ h)
        · exact Or.inr ⟨a, congrArg _ h, ha⟩

end CoherentLadders
end KnightModel.RankTwo
