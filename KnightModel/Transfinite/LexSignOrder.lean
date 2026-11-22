import KnightModel.Transfinite.LexSign
import Mathlib.Order.RelClasses

/-! # Linearizing a tame family of word evaluations -/

namespace KnightModel.Transfinite.LexSign
open RankTwo RankTwo.Semilinear RankTwo.UnaryChoice

structure Laws {F : Type*} (r : F → F → Prop) : Prop where
  asymm : ∀ {a b}, r a b → ¬ r b a
  trans : ∀ {a b c}, r a b → r b c → r a c
  cotrans : ∀ {a c} b, r a c → r a b ∨ r b c

variable {F D : Type*} [LinearOrder D]

abbrev Before (R : F → F → D → Prop) (a b : F) := First (R a b) (R b a)

abbrev Detect (R : F → F → D → Prop) := ∀ a b, (∃ t, R a b t ∨ R b a t) →
  Before R a b ∨ Before R b a

private theorem first_trans {R : F → F → D → Prop} (H : ∀ t, Laws (fun a b => R a b t))
    {a b c} (ab : Before R a b) (bc : Before R b c) : Before R a c := by
  obtain ⟨x,hx,nx⟩ := ab
  obtain ⟨y,hy,ny⟩ := bc
  have early (s : D) (ex : s ≤ x) (ey : s ≤ y) : ¬R c a s := fun h =>
    ((H s).cotrans b h).elim (ny s ey) (nx s ex)
  rcases le_total x y with h | h
  · exact ⟨x, ((H x).cotrans c hx).resolve_right (ny x h),fun s hs => early s hs (hs.trans h)⟩
  · exact ⟨y, ((H y).cotrans a hy).resolve_left (nx y h),fun s hs => early s (hs.trans h) hs⟩

private theorem first_congr_right {R : F → F → D → Prop} (H : ∀ t, Laws (fun a b => R a b t))
    {a b c} (eqv : ∀ t, ¬R a b t ∧ ¬R b a t) : Before R c a ↔ Before R c b := by
  have tr (u v : F) (h : ∀ t, ¬R u v t ∧ ¬R v u t) : Before R c u → Before R c v := by
    rintro ⟨x,hx,ex⟩
    exact ⟨x,((H x).cotrans v hx).resolve_right (h x).2,fun s hs hh =>
      (ex s hs) (((H s).cotrans u hh).resolve_left (h s).2)⟩
  exact ⟨tr _ _ eqv,tr _ _ (fun t => (eqv t).symm)⟩

private theorem first_congr_left {R : F → F → D → Prop} (H : ∀ t, Laws (fun a b => R a b t))
    {a b c} (eqv : ∀ t, ¬R a b t ∧ ¬R b a t) : Before R a c ↔ Before R b c := by
  have tr (u v : F) (h : ∀ t, ¬R u v t ∧ ¬R v u t) : Before R u c → Before R v c := by
    rintro ⟨x,hx,ex⟩
    exact ⟨x,((H x).cotrans v hx).resolve_left (h x).1,fun s hs hh =>
      (ex s hs) (((H s).cotrans u hh).resolve_right (h s).1)⟩
  exact ⟨tr _ _ eqv,tr _ _ (fun t => (eqv t).symm)⟩

theorem before_laws {R : F → F → D → Prop} (H : ∀ t, Laws (fun a b => R a b t))
    (det : Detect R) : Laws (Before R) := by
  refine ⟨First.asymm,first_trans H,?_⟩
  intro a c b hac
  by_contra! h
  have flip (u v) (huv : ¬Before R u v) : Before R v u ∨ (∀ t, ¬R u v t ∧ ¬R v u t) := by
    by_cases ex : ∃ t, R u v t ∨ R v u t
    · exact .inl ((det _ _ ex).resolve_left huv)
    · exact .inr (fun t => ⟨fun ht => ex ⟨t,.inl ht⟩,fun ht => ex ⟨t,.inr ht⟩⟩)
  rcases flip a b h.1 with ba | tied
  · rcases flip b c h.2 with cb | tied
    · exact First.asymm hac (first_trans H cb ba)
    · exact h.1 ((first_congr_right H tied).mpr hac)
  · exact h.2 ((first_congr_left H tied).mp hac)

variable {V : Type*} [LinearOrder V] [AddCommGroup V] [Module ℚ V] [IsOrderedAddMonoid V]
    [PosSMulStrictMono ℚ V]

abbrev Slice (R : F → F → List V → Prop) (n : Nat) (w : List V) (a b : F) :=
  Ahead n (R a b) (R b a) w

private theorem slice_detect (qe : HeadElimination V) {R : F → F → List V → Prop}
    (test : ∀ a b, WordTest (R a b)) (n : Nat) (w : List V)
    (asymmetry : ∀ t, Laws (Slice R n (t :: w))) :
    Detect (fun a b t => Slice R n (t :: w) a b) := by
  intro a b ex
  obtain ⟨E,hp⟩ := thresholds (ahead_definable qe n (test a b) (test b a)) w
  obtain ⟨D,hq⟩ := thresholds (ahead_definable qe n (test b a) (test a b)) w
  exact first_or_first (E++D)
    (fun x y hc => hp x y fun z hz => hc _ (List.mem_append_left _ hz))
    (fun x y hc => hq x y fun z hz => hc _ (List.mem_append_right _ hz))
    (fun t => (asymmetry t).asymm) ex

theorem slice_laws (qe : HeadElimination V) {R : F → F → List V → Prop}
    (test : ∀ a b, WordTest (R a b)) (laws : ∀ w, Laws (fun a b => R a b w))
    (n : Nat) (w : List V) : Laws (Slice R n w) := by
  induction n generalizing w with
  | zero => exact laws w
  | succ n ih => exact before_laws (fun t => ih (t :: w)) (slice_detect qe test n w (fun t => ih _))

/-- Word length has priority over fixed-shape signs. In particular strict
comparison at the empty word already decides the final ordering. -/
abbrev Earlier (R : F → F → List V → Prop) (a b : F) :=
  Before (fun f g n => Slice R n [] f g) a b

private theorem nat_detect {R : F → F → Nat → Prop}
    (ha : ∀ a b t, R a b t → ¬R b a t) : Detect R := by
  classical
  intro a b ex
  let t := Nat.find ex
  have early (i) (hi : i < t) : ¬(R a b i ∨ R b a i) := Nat.find_min ex hi
  rcases Nat.find_spec ex with h | h
  · exact .inl ⟨t,h,fun i hi => if he : i = t then he ▸ ha a b t h else
      fun q => early i (lt_of_le_of_ne hi he) (.inr q)⟩
  · exact .inr ⟨t,h,fun i hi => if he : i = t then he ▸ ha b a t h else
      fun q => early i (lt_of_le_of_ne hi he) (.inl q)⟩

variable (R : F → F → List V → Prop)

private theorem slice_separates (qe : HeadElimination V) (test : ∀ a b, WordTest (R a b))
    (laws : ∀ w, Laws (fun a b => R a b w)) {a b : F} (v w : List V)
    (h : R a b (v.reverse ++ w) ∨ R b a (v.reverse ++ w)) :
    Slice R v.length w a b ∨ Slice R v.length w b a := by
  induction v generalizing w with
  | nil => simpa [Slice,Ahead] using h
  | cons t v ih =>
    apply slice_detect qe test v.length w (fun _ => slice_laws qe test laws _ _)
    exact ⟨t,ih _ (by simpa [List.append_assoc] using h)⟩

/-- An intrinsic linear order for every point-separating, semilinear family
of comparisons. Invalid word arguments may tie all its elements. -/
noncomputable abbrev linearOrder (qe : HeadElimination V) (test : ∀ a b, WordTest (R a b))
    (laws : ∀ w, Laws (fun a b => R a b w))
    (sep : ∀ {a b}, a ≠ b → ∃ w, R a b w ∨ R b a w) : LinearOrder F := by
  classical
  have As (a b : F) (n : Nat) := (slice_laws qe test laws n []).asymm (a:=a) (b:=b)
  have H := before_laws (fun n => slice_laws qe test laws n []) (nat_detect As)
  letI : IsStrictTotalOrder F (Earlier R) :=
    { irrefl := fun a h => H.asymm h h
      trans := fun _ _ _ => H.trans
      trichotomous := by
        intro a b nab nba
        by_contra ne
        obtain ⟨w,hw⟩ := sep ne
        have hs := slice_separates R qe test laws w.reverse [] (a:=a) (b:=b) (by simpa using hw)
        exact ((nat_detect As) a b ⟨_,hs⟩).elim nab nba }
  exact linearOrderOfSTO (Earlier R)

omit [AddCommGroup V] [Module ℚ V] [IsOrderedAddMonoid V] [PosSMulStrictMono ℚ V] in
theorem earlier_of_empty (x y : F) (h : R x y []) (asymmetry : ¬ R y x []) : Earlier R x y :=
  ⟨0,h,fun _ hn => (Nat.eq_zero_of_le_zero hn) ▸ asymmetry⟩

end KnightModel.Transfinite.LexSign
