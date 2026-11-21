import Mathlib.Data.List.Lex
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Order.Group.Basic

/-!
# Finite word charts for the rank-two construction

The alphabet is ordered in its given direction, and the empty word is the greatest word.
A fold uses an order isomorphism from a closed final segment of the alphabet onto the
alphabet. For the nonnegative cone of an ordered group this is subtraction of the endpoint.
-/

namespace KnightModel.RankTwo

/-- Finite words in Kleene–Brouwer order. The two order duals reverse the prefix
comparison while preserving the original comparison of unequal letters. -/
def Word (A : Type*) := List A

namespace Word

variable {A : Type*}

instance [LinearOrder A] : LinearOrder (Word A) :=
  inferInstanceAs (LinearOrder (List Aᵒᵈ)ᵒᵈ)

/-- The empty word. -/
def root : Word A := []

/-- Attach one letter at the front of a word. -/
def cons (a : A) (w : Word A) : Word A := a :: w

/-- Attach a finite prefix. -/
def prepend (s : List A) (w : Word A) : Word A := List.append (α := A) s w

@[simp] theorem prepend_nil (w : Word A) : prepend [] w = w := rfl

@[simp] theorem prepend_cons (a : A) (s : List A) (w : Word A) :
    prepend (a :: s) w = cons a (prepend s w) := rfl

variable [LinearOrder A]

@[simp] theorem cons_lt_root (a : A) (w : Word A) : cons a w < root := List.nil_lt_cons _ _

theorem le_root (w : Word A) : w ≤ root := by
  cases w with
  | nil => exact le_rfl
  | cons a w => exact (cons_lt_root a w).le

instance : OrderTop (Word A) where
  top := root
  le_top := le_root

@[simp] theorem cons_lt_cons_iff {a b : A} {u v : Word A} :
    cons a u < cons b v ↔ a < b ∨ a = b ∧ u < v := by
  change (show List Aᵒᵈ from b :: v) < (show List Aᵒᵈ from a :: u) ↔ _
  rw [List.cons_lt_cons_iff]
  exact or_congr Iff.rfl (and_congr eq_comm Iff.rfl)

@[simp] theorem cons_lt_cons_self {a : A} {u v : Word A} :
    cons a u < cons a v ↔ u < v := by simp

@[simp] theorem cons_le_cons_iff {a b : A} {u v : Word A} :
    cons a u ≤ cons b v ↔ a < b ∨ a = b ∧ u ≤ v := by
  rw [le_iff_lt_or_eq, cons_lt_cons_iff]
  change _ ∨ a :: (u : List A) = b :: (v : List A) ↔ _
  rw [List.cons.injEq, le_iff_lt_or_eq]
  tauto

@[simp] theorem cons_le_cons_self {a : A} {u v : Word A} :
    cons a u ≤ cons a v ↔ u ≤ v := by simp

@[simp] theorem prepend_lt_prepend_iff (s : List A) {u v : Word A} :
    prepend s u < prepend s v ↔ u < v := by induction s <;> simp [*]

@[simp] theorem prepend_le_prepend_iff (s : List A) {u v : Word A} :
    prepend s u ≤ prepend s v ↔ u ≤ v := by induction s <;> simp [*]

/-- Prefix insertion is an order embedding with a convex image. -/
def prependEmbedding (s : List A) : Word A ↪o Word A :=
  OrderEmbedding.ofStrictMono (prepend s) (fun _ _ h => (prepend_lt_prepend_iff s).mpr h)

theorem exists_prepend_of_between (s : List A) {v w y : Word A}
    (h₁ : prepend s v ≤ y) (h₂ : y ≤ prepend s w) :
    ∃ z, prepend s z = y := by
  induction s generalizing y with
  | nil => exact ⟨y, rfl⟩
  | cons a s ih =>
    cases y with
    | nil => exact (not_le_of_gt (cons_lt_root a (prepend s w)) h₂).elim
    | cons b y =>
      have h₁' := cons_le_cons_iff.mp h₁
      have h₂' := cons_le_cons_iff.mp h₂
      rcases h₁' with hab | ⟨rfl, hv⟩
      · rcases h₂' with hba | ⟨rfl, _⟩
        · exact (not_lt_of_gt hab hba).elim
        · exact (lt_irrefl _ hab).elim
      · obtain ⟨z, rfl⟩ := ih hv (cons_le_cons_self.mp h₂)
        exact ⟨z, rfl⟩

theorem ordConnected_range_prepend (s : List A) :
    Set.OrdConnected (Set.range (prepend s)) := by
  constructor
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ y ⟨h₁, h₂⟩
  exact exists_prepend_of_between s h₁ h₂

/-- Insert the current tail chart into the last cone through letter `a`. -/
def foldStep (a : A) (shift : Set.Ici a ≃o A) (f : Word A → Word A) :
    Word A → Word A
  | [] => cons a (f root)
  | b :: w => if h : b < a then cons b w else
      cons a (f (cons (shift ⟨b, le_of_not_gt h⟩) w))

theorem strictMono_foldStep (a : A) (shift : Set.Ici a ≃o A)
    {f : Word A → Word A} (hf : StrictMono f) : StrictMono (foldStep a shift f) := by
  intro x y h
  cases x with
  | nil => exact (not_lt_of_ge (le_root y) h).elim
  | cons b w =>
    cases y with
    | nil =>
      change cons b w < root at h
      by_cases hb : b < a
      · simp [foldStep, hb]
      · simpa [foldStep, hb] using hf (cons_lt_root (shift ⟨b, le_of_not_gt hb⟩) w)
    | cons c v =>
      change cons b w < cons c v at h
      by_cases hb : b < a <;> by_cases hc : c < a
      · simpa only [foldStep, dif_pos hb, dif_pos hc] using h
      · simp only [foldStep, dif_pos hb, dif_neg hc, cons_lt_cons_iff]
        exact .inl hb
      · rcases cons_lt_cons_iff.mp h with hbc | ⟨rfl, _⟩
        · exact (hb (hbc.trans hc)).elim
        · exact (hb hc).elim
      · simp only [foldStep, dif_neg hb, dif_neg hc, cons_lt_cons_self]
        apply hf
        rcases cons_lt_cons_iff.mp h with hbc | ⟨rfl, hwv⟩
        · exact cons_lt_cons_iff.mpr (.inl (shift.strictMono (show
              (⟨b, le_of_not_gt hb⟩ : Set.Ici a) < ⟨c, le_of_not_gt hc⟩ from hbc)))
        · exact cons_lt_cons_self.mpr hwv

/-- A fold step carries a chart through `u` to a chart through `a :: u`. -/
theorem range_foldStep (a : A) (shift : Set.Ici a ≃o A) {f : Word A → Word A}
    {u : Word A} (hf : ∀ z, (∃ w, f w = z) ↔ z ≤ u) (z : Word A) :
    (∃ w, foldStep a shift f w = z) ↔ z ≤ cons a u := by
  constructor
  · rintro ⟨w, rfl⟩
    cases w with
    | nil => exact cons_le_cons_self.mpr ((hf _).mp ⟨_, rfl⟩)
    | cons b v =>
      by_cases hb : b < a
      · simpa only [foldStep, dif_pos hb] using
          (cons_le_cons_iff.mpr (.inl hb) : cons b v ≤ cons a u)
      · simp only [foldStep, dif_neg hb, cons_le_cons_self]
        exact (hf _).mp ⟨_, rfl⟩
  · intro hz
    cases z with
    | nil => exact (not_le_of_gt (cons_lt_root a u) hz).elim
    | cons b v =>
      rcases cons_le_cons_iff.mp hz with hb | ⟨rfl, hv⟩
      · exact ⟨cons b v, by simp [cons, foldStep, hb]⟩
      · obtain ⟨w, hw⟩ := (hf _).mpr hv
        cases w with
        | nil => exact ⟨root, congrArg (cons b) hw⟩
        | cons t w =>
          let c := shift.symm t
          refine ⟨cons c.1 w, ?_⟩
          change (if h : c.1 < b then _ else _) = _
          rw [dif_neg (not_lt_of_ge c.2)]
          change cons b (f (cons (shift c) w)) = cons b v
          simpa [c, cons] using congrArg (cons b) hw

/-- A coordinate map taking the whole word order through any specified word. -/
def through (shift : ∀ a : A, Set.Ici a ≃o A) : Word A → Word A → Word A
  | [] => id
  | a :: u => foldStep a (shift a) (through shift u)

theorem strictMono_through (shift : ∀ a : A, Set.Ici a ≃o A) (u : Word A) :
    StrictMono (through shift u) := by
  induction u with
  | nil => exact strictMono_id
  | cons a u ih => exact strictMono_foldStep a (shift a) ih

theorem range_through (shift : ∀ a : A, Set.Ici a ≃o A) (u z : Word A) :
    (∃ w, through shift u w = z) ↔ z ≤ u := by
  induction u generalizing z with
  | nil => exact ⟨fun _ => le_root z, fun _ => ⟨z, rfl⟩⟩
  | cons a u ih => exact range_foldStep a (shift a) ih z

/-- The fold is an order isomorphism onto the full principal initial segment. -/
noncomputable def throughIso (shift : ∀ a : A, Set.Ici a ≃o A) (u : Word A) :
    Word A ≃o Set.Iic u :=
  let f (w : Word A) : Set.Iic u :=
    ⟨through shift u w, (range_through shift u _).mp ⟨w, rfl⟩⟩
  have hm : StrictMono f := fun _ _ h => strictMono_through shift u h
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := (range_through shift u z.1).mpr z.2
    exact ⟨w, Subtype.ext hw⟩
  { toEquiv := Equiv.ofBijective f ⟨hm.injective, hs⟩
    map_rel_iff' := hm.le_iff_le }

@[simp] theorem through_root (shift : ∀ a : A, Set.Ici a ≃o A) (u : Word A) :
    through shift u root = u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (cons a) ih

section Alphabet
variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- The nonnegative alphabet used for the word charts. -/
abbrev Letter (V : Type*) [Zero V] [Preorder V] := Set.Ici (0 : V)

/-- Subtract a lower endpoint to identify its closed tail with the whole alphabet. -/
def shiftLetter (a : Letter V) : Set.Ici a ≃o Letter V where
  toFun t := ⟨t.1.1 - a.1, sub_nonneg.mpr t.2⟩
  invFun t := ⟨⟨t.1 + a.1, add_nonneg t.2 a.2⟩, le_add_of_nonneg_left t.2⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; exact sub_add_cancel _ _
  right_inv t := by apply Subtype.ext; exact add_sub_cancel_right _ _
  map_rel_iff' := by
    intro s t
    change s.1.1 - a.1 ≤ t.1.1 - a.1 ↔ s.1.1 ≤ t.1.1
    exact sub_le_sub_iff_right _

end Alphabet
end Word
end KnightModel.RankTwo
