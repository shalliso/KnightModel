import KnightModel.RankTwo.Walk

/-! # Finite prefix substitutions on the ordinal skeleton -/

namespace KnightModel.RankTwo.CoherentLadders

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)

/-- A final segment below a limit index is copied by a single prefix. -/
def CopiesTail (b d : J) (s : List A) : Prop :=
  ∃ n < d, ∀ x, n < x → x < d → C.word b x = s ++ C.word d x

/-- The copied prefix is unique at a genuine limit. Right cancellation uses
only one target in the common final interval. -/
theorem copiesTail_unique {b d : J} {s t : List A}
    (hlim : ∀ n < d, ∃ x, n < x ∧ x < d)
    (hs : C.CopiesTail b d s) (ht : C.CopiesTail b d t) : s = t := by
  obtain ⟨n, hn, hs⟩ := hs
  obtain ⟨m, hm, ht⟩ := ht
  obtain ⟨x, hnx, hxd⟩ := hlim (max n m) (max_lt hn hm)
  exact List.append_cancel_right <| (hs x ((le_max_left _ _).trans_lt hnx) hxd).symm.trans
    (ht x ((le_max_right _ _).trans_lt hnx) hxd)

/-- An enclosing copied interval prepends its prefix to that of every interior
limit sector. This is the covariance used to glue those sectors. -/
theorem copiesTail_inside {b c d n : J} {p s : List A} (hnd : n < d) (hdc : d < c)
    (hp : ∀ x, n < x → x < c → C.word b x = p ++ C.word c x)
    (hs : C.CopiesTail c d s) : C.CopiesTail b d (p ++ s) := by
  obtain ⟨m, hm, hs⟩ := hs
  refine ⟨max n m, max_lt hnd hm, ?_⟩
  intro x hnx hxd
  rw [hp x ((le_max_left _ _).trans_lt hnx) (hxd.trans hdc),
    hs x ((le_max_right _ _).trans_lt hnx) hxd, List.append_assoc]

/-- A guard for one coordinate substitution on the marked ordinal sequence.
Open guards are needed at limit indices, whose endpoint gets a separate rule. -/
inductive WalkGuard (J : Type*) where
  | point (x : J)
  | between (l r : J)

def WalkGuard.Holds (g : WalkGuard J) (x : J) : Prop :=
  match g with
  | .point z => x = z
  | .between l r => l < x ∧ x < r

/-- A rule removes `source` and inserts `target`, keeping the suffix. -/
structure PrefixRule (J A : Type*) where
  guard : WalkGuard J
  source : List A
  target : List A

def PrefixRule.Valid (b c : J) (r : PrefixRule J A) : Prop :=
  ∀ x, r.guard.Holds x → ∃ w, C.word b x = r.source ++ w ∧ C.word c x = r.target ++ w

/-- The two actual walk charts on an entire initial interval differ by
finitely many guarded prefix substitutions. The rules are valid on their whole
guards, including the singleton guard at the terminal index. -/
theorem finite_prefix_rules {b c d : J} (hdb : d ≤ b) (hdc : d ≤ c) :
    ∃ rs : List (PrefixRule J A),
      (∀ r ∈ rs, PrefixRule.Valid C b c r) ∧
      (∀ x, x ≤ d ↔ ∃ r ∈ rs, r.guard.Holds x) := by
  classical
  induction d using (wellFounded_lt (α := J)).induction with
  | h d ih =>
    let atD : PrefixRule J A := ⟨.point d, C.word b d, C.word c d⟩
    have hdok : PrefixRule.Valid C b c atD := by
      intro x hx
      change x = d at hx
      subst x
      exact ⟨[], by simp [atD], by simp [atD]⟩
    by_cases below : ∃ n, n < d
    · obtain ⟨s, ⟨n, hn, hs⟩, _⟩ := C.tail hdb below
      obtain ⟨t, ⟨m, hm, ht⟩, _⟩ := C.tail hdc below
      have hu : max n m < d := max_lt hn hm
      obtain ⟨rs, hrs, hcover⟩ := ih (max n m) hu (hu.le.trans hdb) (hu.le.trans hdc)
      let mid : PrefixRule J A := ⟨.between (max n m) d, s, t⟩
      have hmok : PrefixRule.Valid C b c mid := by
        intro x hx
        change max n m < x ∧ x < d at hx
        exact ⟨C.word d x, hs x ((le_max_left _ _).trans_lt hx.1) hx.2,
          ht x ((le_max_right _ _).trans_lt hx.1) hx.2⟩
      refine ⟨atD :: mid :: rs, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | hr
        · exact hdok
        · exact hmok
        · exact hrs r hr
      · intro x
        simp only [List.mem_cons]
        constructor
        · intro hxd
          rcases hxd.lt_or_eq with hlt | rfl
          · by_cases hx : x ≤ max n m
            · obtain ⟨r, hr, hg⟩ := (hcover x).mp hx
              exact ⟨r, Or.inr (Or.inr hr), hg⟩
            · exact ⟨mid, Or.inr (Or.inl rfl), lt_of_not_ge hx, hlt⟩
          · exact ⟨atD, Or.inl rfl, rfl⟩
        · rintro ⟨r, hr, hg⟩
          rcases hr with rfl | rfl | hr
          · exact le_of_eq hg
          · exact hg.2.le
          · exact ((hcover x).mpr ⟨r, hr, hg⟩).trans hu.le
    · refine ⟨[atD], ?_, ?_⟩
      · intro r hr
        have he := List.mem_singleton.mp hr
        exact he ▸ hdok
      · intro x
        constructor
        · intro hx
          have he : x = d := hx.eq_of_not_lt (fun hx => below ⟨x, hx⟩)
          exact ⟨atD, List.mem_singleton_self _, he⟩
        · rintro ⟨r, hr, hg⟩
          have he := List.mem_singleton.mp hr
          subst r
          exact le_of_eq hg

end KnightModel.RankTwo.CoherentLadders
