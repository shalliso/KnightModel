import KnightModel.RankTwo.WordEvaluation
import KnightModel.RankTwo.ProgramDefinability

/-! # Uniform finite graph bounds for coordinate schemes -/

namespace KnightModel.RankTwo

open Set

namespace PrefixBounds

theorem congr {A : Type*} {R S : List A → List A → Prop} {k : ℕ}
    (h : PrefixBounds R k) (e : ∀ x y, R x y ↔ S x y) : PrefixBounds S k := by
  obtain rfl : R = S := by funext x y; exact propext (e x y)
  exact h

end PrefixBounds

namespace Word

variable {A : Type*} [LinearOrder A]
variable (shift : ∀ a : A, Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Ioi a ≃o Ioi o)

omit [LinearOrder A] in
theorem prefixBounds_prepend (p : List A) :
    PrefixBounds (fun x y : List A => prepend p x = y) p.length where
  sizes := by rintro x _ rfl; simp [prepend,List.length_append]; omega
  snoc x y _ _ a b := by
    change p ++ (x ++ [a]) = y ++ [b] ↔ _
    rw [← List.append_assoc, List.append_eq_append_iff_of_size_eq_right (by simp)]
    simp [prepend,and_comm]
    tauto

theorem prefixBounds_through (u : Word A) :
    PrefixBounds (fun x y : List A => through shift u x = y) (List.length u) where
  sizes := by
    rintro x _ rfl
    exact ⟨(length_le_through shift u x).trans (Nat.le_add_right ..), length_through_le shift u x⟩
  snoc x y hx _ a b := by
    have he := through_inspects shift u x [a] hx
    change some (through shift u (x ++ [a])) = some (List.append (α := A) (through shift u x) [a]) at he
    change through shift u (x ++ [a]) = y ++ [b] ↔ _
    rw [Option.some.inj he]
    let z : List A := through shift u x
    change z ++ [a] = y ++ [b] ↔ a = b ∧ z = y
    rw [List.append_eq_append_iff_of_size_eq_right (by simp)]
    simp [and_comm]

theorem prefixBounds_single (a : A) : PrefixBounds (SingleGraph o upper a) 1 where
  sizes := by
    rintro x y h
    cases x with
    | nil =>
      obtain rfl := (singleGraph_root o upper a y).mp h
      simp [root]
    | cons t w =>
      obtain ⟨_,rfl⟩ := (singleGraph_cons o upper a t w y).mp h
      simp [cons]
  snoc x y hx _ a' b' := by
    cases x with
    | nil => simp at hx
    | cons t w =>
      change SingleGraph o upper a (cons t (w ++ [a'])) (y ++ [b']) ↔ _ ∧ SingleGraph o upper a (cons t w) y
      rw [singleGraph_cons,singleGraph_cons]
      constructor
      · rintro ⟨ht,h⟩
        have e : y ++ [b'] = ((((upper a).symm ⟨t,ht⟩).val :: w) ++ [a']) := h
        rw [List.append_eq_append_iff_of_size_eq_right (by simp)] at e
        exact ⟨(List.cons.inj e.2).1.symm,ht,e.1⟩
      · rintro ⟨rfl,ht,rfl⟩
        exact ⟨ht,rfl⟩

/-- The graph bound depends only on the endpoint length, even when the point
lies in a different summand at each level. -/
theorem prefixBounds_tail (v : Word A) :
    PrefixBounds (TailGraph shift o d hd upper v) (2 * List.length v + 2) := by
  induction v with
  | nil =>
    apply (PrefixBounds.empty.mono (Nat.zero_le _)).congr
    intro x y
    simp [TailGraph,root]
  | cons a v ih =>
    cases v with
    | nil =>
      exact ((prefixBounds_single o upper a).mono (by decide : 1 ≤ 2*1+2)).congr
        (fun x y => (tailGraph_singleton shift o d hd upper a x y).symm)
    | cons b w =>
      let first := (prefixBounds_through shift (cons d root)).inv.seq
        (ih.seq (prefixBounds_prepend [a]))
      let last := (prefixBounds_single o upper d).inv.seq (prefixBounds_single o upper a)
      have both := first.union last
      have hb : max (List.length (cons d root) + (2 * (b :: w).length + 2 + [a].length)) (1+1)
          ≤ 2 * (a :: b :: w).length + 2 := by simp [cons,root]; omega
      apply (both.mono hb).congr
      intro x y
      refine Iff.trans ?_ (tailGraph_cons shift o d hd upper a b w x y).symm
      apply or_congr _ Iff.rfl
      constructor
      · rintro ⟨t,ht,z,hz,h⟩
        exact ⟨t,z,ht,hz,h⟩
      · rintro ⟨t,z,ht,hz,h⟩
        exact ⟨t,ht,z,hz,h⟩


private theorem prefixBounds_interval (v u : Word A) (h : v < u) :
    PrefixBounds (fun x y : Word A => ∃ z : Ioi (cons o root),
      x = z.val ∧ y = (intervalIso shift o d hd upper h z).val)
        (2 * List.length v + 2 + List.length u) := by
  let t := (throughIso shift u).symm ⟨v,h.le⟩
  have ht : through shift u t = v := congrArg (fun q : Iic u => q.val)
    ((throughIso shift u).apply_symm_apply ⟨v,h.le⟩)
  have hb : List.length t ≤ List.length v := ht ▸ length_le_through shift u t
  have whole := (prefixBounds_tail shift o d hd upper t).seq (prefixBounds_through shift u)
  apply (whole.mono (show 2 * List.length t + 2 + List.length u ≤ _ by omega)).congr
  intro x y
  refine Iff.trans ?_ (interval_graph shift o d hd upper v u h x y).symm
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨t,z,ht,hz,he⟩
  · rintro ⟨s,z,hs,hz,he⟩
    obtain rfl : s = t := (strictMono_through shift u).injective (hs.trans ht.symm)
    exact ⟨z,hz,he⟩

theorem prefixBounds_H (v u : Word A) :
    PrefixBounds (HGraph shift o d hd upper v u)
      (2 * List.length v + 2 + List.length u) := by
  have base (v u : Word A) (e : ∀ h : v < u,
      H shift o d hd upper v u h = intervalIso shift o d hd upper h) :
      PrefixBounds (HGraph shift o d hd upper v u)
        (2 * List.length v + 2 + List.length u) := by
    by_cases h : v < u
    · apply (prefixBounds_interval shift o d hd upper v u h).congr
      intro x y
      constructor
      · rintro ⟨z,hx,hy⟩
        exact ⟨h,z,hx,(e h) ▸ hy⟩
      · rintro ⟨_,z,hx,hy⟩
        exact ⟨z,hx,(e h) ▸ hy⟩
    · apply (PrefixBounds.empty.mono (Nat.zero_le _)).congr
      exact fun _ _ => ⟨False.elim,fun ⟨hu,_⟩ => h hu⟩
  induction v generalizing u with
  | nil => exact base root u (fun h => (not_lt_of_ge (le_root u) h).elim)
  | cons a v ih =>
    cases u with
    | nil => exact base _ root (H_at_root shift o d hd upper _)
    | cons b u =>
      by_cases hab : a = b
      · subst b
        have h := (ih u).seq (prefixBounds_prepend [a])
        have hb : 2*v.length + 2 + u.length + [a].length ≤
            2*(a::v).length + 2 + (a::u).length := by simp; omega
        exact (h.mono hb).congr (fun x y => (hgraph_common shift o d hd upper a v u x y).symm)
      · exact base _ _ (fun h => H_different shift o d hd upper a b v u h hab)

private theorem prefixBounds_guard {p : List A → Prop} {k : ℕ}
    (s : ∀ x : List A, k ≤ x.length → ∀ a, p (x ++ [a]) ↔ p x) :
    PrefixBounds (fun x y => p x ∧ x = y) k where
  sizes := by rintro x _ ⟨_,rfl⟩; simp
  snoc x y hx _ a b := by
    rw [s x hx a, List.append_eq_append_iff_of_size_eq_right (by simp)]
    simp only [List.cons.injEq, and_true]
    tauto

theorem lt_append_iff (v : Word A) (x : List A) (h : List.length v < x.length)
    (r : List A) : @LT.lt (Word A) _ v (x ++ r) ↔ @LT.lt (Word A) _ v x := by
  induction v generalizing x with
  | nil => exact ⟨fun hx => (not_lt_of_ge (le_root _) hx).elim,
      fun hx => (not_lt_of_ge (le_root _) hx).elim⟩
  | cons a v ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      change cons a v < cons b (x ++ r) ↔ cons a v < cons b x
      rw [cons_lt_cons_iff,cons_lt_cons_iff]
      exact or_congr Iff.rfl (and_congr Iff.rfl (ih x (by simpa using h)))

theorem prefixBounds_above (v : Word A) :
    PrefixBounds (fun x y : List A => @LT.lt (Word A) _ v x ∧ x = y) (List.length v + 1) :=
  prefixBounds_guard (fun x h a => lt_append_iff v x h [a])

theorem prefixBounds_atMost (v : Word A) :
    PrefixBounds (fun x y : List A => @LE.le (Word A) _ x v ∧ x = y) (List.length v + 1) :=
  prefixBounds_guard (fun x h a => (not_congr (lt_append_iff v x h [a])).trans' not_lt.symm |>.trans not_lt)

end Word
end KnightModel.RankTwo
