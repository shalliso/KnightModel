/-
Copyright (c) 2026 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import KnightModel.KnightAutGroup.KnightCondition
import Mathlib

/-!
# Dense Sets for the Knight Group Construction

In the Rasiowa-Sikorski / Cohen forcing argument that produces a generic knight group,
we need our generic filter to meet four families of dense open sets in `KnightCondition`.
This file defines those four families and proves that each one is dense and open.

## The four families

* **`inDomain n a`**: conditions `p` for which `a` already appears in the domain of `p.seq n`.
  Density guarantees that every generic automorphism `genericAut n` is eventually defined at
  every rational `a`, making `genericAut n` a total function.

* **`inRange n a`**: conditions `p` for which `a` appears in the range of `p.seq n`.
  Dually, this ensures `genericAut n` is surjective.

* **`connects a b`**: conditions `p` under which some word `w` evaluates `a` to `b`.
  Density here produces, for every pair `(a, b)`, a group element (encoded by `wordToAut w`)
  sending `a` to `b` — giving transitivity of the knight group.

* **`decrements a b c`**: conditions `p` under which some word fixes `a` and sends `c`
  strictly below `b`. Density here realizes the density axiom for the knight group: for
  every `a < b < c`, a generic group element fixes `a` and moves `c` below `b`.

## Main results

* `inDomain_open`, `inRange_open`, `connects_open`, `decrements_open`: each family is upward
  closed (open in the specialisation order, i.e. stable under extension).
* `inDomain_dense`, `inRange_dense`, `connects_dense`, `decrements_dense`: each family is dense,
  meaning every condition has an extension belonging to the family.

## Tags

knight group, dense sets, forcing, generic filter
-/

namespace KnightCondition

def inDomain (n : ℕ) (a : ℚ) : Set KnightCondition :=
  {p | ∃ b, (a, b) ∈ (p.seq n).graph}

lemma inDomain_open {n : ℕ} {a : ℚ} {p q : KnightCondition}
    (hp : p ∈ inDomain n a) (hpq : q ≤ p) : q ∈ inDomain n a := by
  obtain ⟨b, hb⟩ := hp
  exact ⟨b, hpq n hb⟩

/-- If `evalWord p w a = some b`, then either `b = a` or `b` appears in the domain or range of
some `p m`. In particular, if `b` is fresh (not in any dom/ran) and `b ≠ a`, then
`evalWord p w a ≠ some b`. -/
private lemma evalWord_result_mem_or_eq (p : Condition) (w : Word) (a b : ℚ)
    (h : evalWord p w a = some b) :
    b = a ∨ b ∈ ⋃ m, (p m).dom ∪ (p m).ran := by
  induction w generalizing a with
  | nil =>
    simp only [evalWord] at h
    exact Or.inl (Option.some.inj h).symm
  | cons l w' ih =>
    simp only [evalWord] at h
    obtain ⟨m, dir⟩ := l
    cases dir with
    | false =>
      simp only [evalLetter] at h
      cases hc : (p m).apply? a with
      | none => simp [hc] at h
      | some c =>
        rw [hc] at h
        simp only [Option.bind_some] at h
        rcases ih c h with heq | hbran
        · exact Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_union_right _
            ⟨a, heq ▸ PartialInj.mem_graph_of_apply? hc⟩⟩)
        · exact Or.inr hbran
    | true =>
      simp only [evalLetter] at h
      cases hc : (p m).inv.toPartialInj.apply? a with
      | none => simp [hc] at h
      | some c =>
        rw [hc] at h
        simp only [Option.bind_some] at h
        have hca_mem : (c, a) ∈ (p.seq m).graph := by
          have hmem := PartialInj.mem_graph_of_apply? hc
          exact hmem
        rcases ih c h with heq | hbran
        · exact Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_union_left _
            ⟨a, heq ▸ hca_mem⟩⟩)
        · exact Or.inr hbran

private lemma forbidden_finite (p : KnightCondition) :
    (⋃ m, ((p.seq m).dom ∪ (p.seq m).ran)).Finite := by
  apply Set.Finite.subset
    (p.finite_support.biUnion (fun m _ =>
      ((p.finite m).image Prod.fst).union ((p.finite m).image Prod.snd)))
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  simp only [Set.mem_union] at hm
  rcases hm with hdom | hran
  · obtain ⟨b, hb⟩ := hdom
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_image]
    have hemp : p.seq m ≠ ∅ := by
      intro heq
      have hg : (p.seq m).graph = ∅ := by rw [heq]; rfl
      simp [hg] at hb
    exact ⟨m, hemp, Or.inl ⟨(x, b), hb, rfl⟩⟩
  · obtain ⟨a, ha⟩ := hran
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_image]
    have hemp : p.seq m ≠ ∅ := by
      intro heq
      have hg : (p.seq m).graph = ∅ := by rw [heq]; rfl
      simp [hg] at ha
    exact ⟨m, hemp, Or.inr ⟨(a, x), ha, rfl⟩⟩

private lemma infinite_between_finsets (lo hi : Finset ℚ)
    (hlo_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y) :
    Set.Infinite {x : ℚ | (∀ l ∈ lo, l < x) ∧ (∀ h ∈ hi, x < h)} := by
  obtain ⟨b₀, hb₀lo, hb₀hi⟩ := Order.exists_between_finsets lo hi hlo_hi
  obtain ⟨b₁, hb₁lo, hb₁hi⟩ := Order.exists_between_finsets (lo ∪ {b₀}) hi (by
    intro x hx y hy
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with hxlo | rfl
    · exact hlo_hi x hxlo y hy
    · exact hb₀hi y hy)
  apply (Set.Ioo_infinite (show b₀ < b₁ from
    hb₁lo b₀ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))).mono
  intro x hx
  simp only [Set.mem_Ioo] at hx
  exact ⟨fun l hl => lt_trans (hb₀lo l hl) hx.1,
         fun h hh => lt_trans hx.2 (hb₁hi h hh)⟩

/-- Given finsets `lo`, `hi` with all elements of `lo` below all elements of `hi`,
    and a `KnightCondition` `p` and a point `a`, there exists a rational `b` strictly
    between `lo` and `hi` that lies outside the (finite) support of `p` and differs from `a`. -/
private lemma exists_fresh_between (lo hi : Finset ℚ)
    (hlo_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y)
    (p : KnightCondition) (a : ℚ) :
    ∃ b : ℚ, (∀ l ∈ lo, l < b) ∧ (∀ h ∈ hi, b < h) ∧
      (∀ m, b ∉ (p.seq m).dom ∧ b ∉ (p.seq m).ran) ∧ b ≠ a := by
  obtain ⟨b, hb_mem⟩ :=
    ((infinite_between_finsets lo hi hlo_hi).sdiff
      ((forbidden_finite p).union (Set.finite_singleton a))).nonempty
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
             Set.mem_singleton_iff] at hb_mem
  push Not at hb_mem
  obtain ⟨⟨hb_lo, hb_hi⟩, hb_fresh, hb_ne_a⟩ := hb_mem
  exact ⟨b, hb_lo, hb_hi, hb_fresh, hb_ne_a⟩

/-- If `(p.seq n)` has a fixed point `c` with `a ≤ c`, then `p` can be extended
    at index `n` by adding the pair `(a, a)`. -/
private lemma canExtend_self_of_fixed_point (p : KnightCondition) (n : ℕ) (a : ℚ)
    (ha : a ∉ (p.seq n).dom)
    (hfixed : ∃ c, (c, c) ∈ (p.seq n).graph ∧ a ≤ c) :
    p.CanExtend n a a := by
  refine { toCanExtendFPA := ?_, noNewCycles := Or.inl rfl }
  let f : FixingPartialAut ℚ := p.seq n
  refine { freshDom := ha, freshRan := ?_, orderCompat := ?_, fixingCompat := ?_ }
  · -- freshRan: a ∉ (p.seq n).ran
    intro ⟨b, hb⟩
    obtain ⟨c, hc, hac⟩ := hfixed
    have hbc : b ≤ c := ((p.seq n).order_pres_iff hb hc).mpr hac
    have hba : b = a := f.fixing (c, c) hc (b, a) hb rfl hbc
    exact ha ⟨b, hba ▸ hb⟩
  · -- orderCompat: ∀ p_1 ∈ (p.seq n).graph, p_1.1 ≤ a ↔ p_1.2 ≤ a
    intro ⟨x, y⟩ hxy
    obtain ⟨c, hc, hac⟩ := hfixed
    by_cases hxc : x ≤ c
    · -- x ≤ c: by fixing, x = y, so iff is trivial
      have hxy_eq : x = y := (p.seq n).fixing (c, c) hc (x, y) hxy rfl hxc
      simp [hxy_eq]
    · -- c < x: both sides false
      push Not at hxc
      have hxa : ¬(x ≤ a) := not_le.mpr (lt_of_le_of_lt hac hxc)
      have hcy : c ≤ y := (p.seq n).order_pres (c, c) hc (x, y) hxy (le_of_lt hxc)
      have hay : a ≤ y := le_trans hac hcy
      have hya : y ≠ a := fun heq =>
        (not_le.mpr hxc) (((p.seq n).order_pres_iff hxy hc).mpr (heq.symm ▸ hac))
      exact iff_of_false hxa (not_le.mpr (lt_of_le_of_ne hay (Ne.symm hya)))
  · -- fixingCompat
    constructor
    · intro _ q hq hqa
      obtain ⟨c, hc, hac⟩ := hfixed
      exact (p.seq n).fixing (c, c) hc q hq rfl (le_trans hqa hac)
    · intro _ _ _ _; rfl

lemma inDomain_dense (n : ℕ) (a : ℚ) (p : KnightCondition) :
    ∃ q ≤ p, q ∈ inDomain n a := by
  -- check if a is already in the domain of p.seq n, in which case we let q = p
  by_cases ha : a ∈ (p.seq n).dom
  · exact ⟨p, le_refl _, ha⟩
  -- Case split on whether (p.seq n) has a fixed point (c, c) with a ≤ c in its graph
  by_cases hfixed : ∃ c, (c, c) ∈ (p.seq n).graph ∧ a ≤ c
  · -- Case 1: fixed point c ≥ a exists; extend p by adding (a, a) at index n
    obtain ⟨q, hqp, hqmem⟩ := (canExtend_self_of_fixed_point p n a ha hfixed).exists_extension
    exact ⟨q, hqp, a, hqmem⟩
  · -- Case 2: no fixed point c ≥ a; choose fresh b between images of points below/above a
    -- Images of domain points strictly below a (lower bound set for b)
    have hgraph_fin : (p.seq n).graph.Finite := p.finite n
    -- Images of domain points strictly below a (lower bound set for b)
    let lo : Finset ℚ := (hgraph_fin.toFinset.filter (fun q => q.1 < a)).image Prod.snd
    -- Images of domain points strictly above a (upper bound set for b)
    let hi : Finset ℚ := (hgraph_fin.toFinset.filter (fun q => a < q.1)).image Prod.snd
    have hlo_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y := by
      intro x hx y hy
      simp only [lo, hi, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset] at hx hy
      obtain ⟨⟨c, xc⟩, ⟨hcgraph, hca⟩, hxc⟩ := hx
      obtain ⟨⟨d, yd⟩, ⟨hdgraph, had⟩, hyd⟩ := hy
      subst hxc; subst hyd
      -- Order-preservation: c < d implies xc ≤ yd
      have hcd : c < d := lt_trans hca had
      have hxy_le : xc ≤ yd := (p.seq n).order_pres (c, xc) hcgraph (d, yd) hdgraph (le_of_lt hcd)
      -- Strict: if xc = yd then injectivity gives c = d, contradiction
      rcases lt_or_eq_of_le hxy_le with h | h
      · exact h
      · exfalso
        have : c = d := (p.seq n).injective (c, xc) hcgraph (d, yd) hdgraph h
        exact absurd this (ne_of_lt hcd)
    obtain ⟨b, hb_lo, hb_hi, hb_fresh, hb_ne_a⟩ := exists_fresh_between lo hi hlo_hi p a
    -- Now build the CanExtend witness
    have hcan : p.CanExtend n a b := by
      refine { freshDom := ha, freshRan := ?_, orderCompat := ?_,
               fixingCompat := ?_, noNewCycles := ?_ }
      · -- freshRan: b ∉ (p.seq n).ran
        exact (hb_fresh n).2
      · -- orderCompat: ∀ (x, y) ∈ (p.seq n).graph, x ≤ a ↔ y ≤ b
        intro ⟨x, y⟩ hxy
        constructor
        · intro hxa
          -- x ≤ a, so x < a (since a ∉ dom implies (x, y) is a pair with x ≠ a)
          -- x is in dom of (p.seq n), so by hb_fresh x ≠ b, and y is in ran, so y ≠ b
          -- Since x ≤ a, x < a (x can't equal a since a ∉ dom), so x ∈ lo, so b > y = Prod.snd
          have hxlt : x < a := lt_of_le_of_ne hxa (fun heq => ha ⟨y, heq ▸ hxy⟩)
          have hlo_mem : y ∈ lo := by
            simp only [lo, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset]
            exact ⟨(x, y), ⟨hxy, hxlt⟩, rfl⟩
          exact le_of_lt (hb_lo y hlo_mem)
        · intro hyb
          -- y ≤ b; by hb_fresh y ≠ b (y ∈ ran), so y < b
          have hyne : y ≠ b := fun heq => (hb_fresh n).2 ⟨x, heq ▸ hxy⟩
          have hylt : y < b := lt_of_le_of_ne hyb hyne
          -- If a ≤ x, then x ∈ hi, so b < y, contradiction
          by_contra hxa
          push Not at hxa
          have hxgt : a < x := hxa
          have hhi_mem : y ∈ hi := by
            simp only [hi, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset]
            exact ⟨(x, y), ⟨hxy, hxgt⟩, rfl⟩
          exact absurd (hb_hi y hhi_mem) (not_lt.mpr (le_of_lt hylt))
      · -- fixingCompat: (a = b → ∀ p ∈ (p.seq n).graph, p.1 ≤ a → p.1 = p.2)
        --               ∧ (∀ p ∈ (p.seq n).graph, p.1 = p.2 → a ≤ p.1 → a = b)
        constructor
        · intro hab
          exact False.elim (hb_ne_a hab.symm)
        · intro ⟨x, y⟩ hxy hxy_eq hax
          exfalso
          simp only [] at hxy_eq
          subst hxy_eq
          exact hfixed ⟨x, hxy, hax⟩
      · -- noNewCycles: a = b ∨ ∀ w, evalWord p w a ≠ some b
        exact Or.inr (fun w hw => by
          rcases evalWord_result_mem_or_eq p.toCondition w a b hw with heq | hmem
          · exact hb_ne_a heq
          · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
            exact hm.elim (hb_fresh m).1 (hb_fresh m).2)
    obtain ⟨q, hqp, hqmem⟩ := hcan.exists_extension
    exact ⟨q, hqp, b, hqmem⟩

def inRange (n : ℕ) (a : ℚ) : Set KnightCondition :=
  {p | ∃ b, (b, a) ∈ (p.seq n).graph}

lemma mem_inRange_iff_inv_mem_inDomain {n : ℕ} {a : ℚ} {p : KnightCondition} :
    p ∈ inRange n a ↔ p⁻¹ ∈ inDomain n a := by
  simp only [inRange, inDomain, Set.mem_setOf_eq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simp [inv_seq, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm, hb]⟩
  · rintro ⟨b, hb⟩
    simp only [inv_seq, FixingPartialAut.inv, PartialIso.symm, PartialInj.symm,
               Set.mem_setOf_eq] at hb
    exact ⟨b, hb⟩

lemma inRange_open {n : ℕ} {a : ℚ} {p q : KnightCondition}
    (hp : p ∈ inRange n a) (hpq : q ≤ p) : q ∈ inRange n a := by
  rw [mem_inRange_iff_inv_mem_inDomain] at hp ⊢
  exact inDomain_open hp (inv_le_inv_iff.mpr hpq)

lemma inRange_dense (n : ℕ) (a : ℚ) (p : KnightCondition) :
    ∃ q ≤ p, q ∈ inRange n a := by
  obtain ⟨q, hq_le, hq_mem⟩ := inDomain_dense n a p⁻¹
  refine ⟨q⁻¹, ?_, ?_⟩
  · exact inv_inv p ▸ inv_le_inv_iff.mpr hq_le
  · exact mem_inRange_iff_inv_mem_inDomain.mpr (inv_inv q ▸ hq_mem)

/-! ## Connects: conditions where a and b are word-connected -/

/-- `p ∈ connects a b` iff some word evaluates `a` to `b` under `p`. -/
def connects (a b : ℚ) : Set KnightCondition :=
  {p | ∃ w : Word, evalWord p w a = some b}

lemma connects_open {a b : ℚ} {p q : KnightCondition}
    (hp : p ∈ connects a b) (hpq : q ≤ p) : q ∈ connects a b := by
  obtain ⟨w, hw⟩ := hp
  exact ⟨w, evalWord_le w a b hpq hw⟩

lemma connects_dense (a b : ℚ) (p : KnightCondition) :
    ∃ q ≤ p, q ∈ connects a b := by
  -- Case 1: p already connects a to b
  by_cases h : p ∈ connects a b
  · exact ⟨p, le_refl _, h⟩
  -- Extract that p does not connect a to b
  simp only [connects, Set.mem_setOf_eq] at h
  push Not at h
  -- Find an index n where p.seq n = ∅
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.seq n = ∅ := by
    obtain ⟨n, hn⟩ := p.finite_support.infinite_compl.nonempty
    exact ⟨n, by simpa [Set.mem_compl_iff] using hn⟩
  -- Build CanExtend at n with the pair (a, b)
  have hcan : p.CanExtend n a b := by
    have hgraph : (p.seq n).graph = ∅ := by rw [hn]; rfl
    refine { toCanExtendFPA := ?_, noNewCycles := Or.inr (fun w hw => h w hw) }
    refine { freshDom := ?_, freshRan := ?_, orderCompat := ?_, fixingCompat := ?_ }
    · exact fun ⟨_, hx⟩ => (Set.mem_empty_iff_false _).mp (hgraph ▸ hx)
    · exact fun ⟨_, hx⟩ => (Set.mem_empty_iff_false _).mp (hgraph ▸ hx)
    · exact fun _ hxy => ((Set.mem_empty_iff_false _).mp (hgraph ▸ hxy)).elim
    · exact ⟨fun _ _ h1 _ => ((Set.mem_empty_iff_false _).mp (hgraph ▸ h1)).elim,
             fun _ h1 _ _ => ((Set.mem_empty_iff_false _).mp (hgraph ▸ h1)).elim⟩
  -- Extend p to q and witness the single-letter word [(n, false)]
  obtain ⟨q, hqp, hqmem⟩ := hcan.exists_extension
  exact ⟨q, hqp, [(n, false)], by
    simp [evalWord, evalLetter, PartialInj.apply?_of_mem hqmem]⟩

/-! ## Decrements: conditions witnessing the Knight density property -/

/-- `p ∈ decrements a b c` iff some word fixes `a` and moves `c` strictly below `b`.
    This formalizes the density axiom for Knight groups: for every `a < b < c` there
    should be a group element fixing `a` and sending `c` below `b`. -/
def decrements (a b c : ℚ) : Set KnightCondition :=
  {p | ∃ w : Word, evalWord p w a = some a ∧ ∃ d : ℚ, evalWord p w c = some d ∧ d < b}

lemma decrements_open {a b c : ℚ} {p q : KnightCondition}
    (hp : p ∈ decrements a b c) (hpq : q ≤ p) : q ∈ decrements a b c := by
  obtain ⟨w, hw_a, d, hw_c, hd⟩ := hp
  exact ⟨w, evalWord_le w a a hpq hw_a,
         d, evalWord_le w c d hpq hw_c, hd⟩

lemma decrements_dense (a b c : ℚ) (habc : a < b) (hbc : b < c)
    (p : KnightCondition) : ∃ q ≤ p, q ∈ decrements a b c := by
  -- Find an index n where p.seq n = ∅
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p.seq n = ∅ := by
    obtain ⟨n, hn⟩ := p.finite_support.infinite_compl.nonempty
    exact ⟨n, by simpa [Set.mem_compl_iff] using hn⟩
  -- Choose d fresh between a and b, not in dom/ran of any p.seq m, and ≠ c
  obtain ⟨d, hda, hdb, hd_fresh, hdc⟩ :=
    exists_fresh_between {a} {b}
      (by simp [habc]) p c
  simp only [Finset.mem_singleton, forall_eq] at hda hdb
  -- hda : a < d,  hdb : d < b,  hd_fresh : ∀ m, d ∉ (p.seq m).dom ∧ d ∉ (p.seq m).ran
  -- hdc : d ≠ c
  have hgraph : (p.seq n).graph = ∅ := by rw [hn]; rfl
  -- First extension: add (c, d) at index n
  have h1can : p.CanExtend n c d := by
    refine { toCanExtendFPA := ?_, noNewCycles := ?_ }
    · refine { freshDom := ?_, freshRan := ?_, orderCompat := ?_, fixingCompat := ?_ }
      · exact fun ⟨_, hx⟩ => (Set.mem_empty_iff_false _).mp (hgraph ▸ hx)
      · exact fun ⟨_, hx⟩ => (Set.mem_empty_iff_false _).mp (hgraph ▸ hx)
      · exact fun _ hxy => ((Set.mem_empty_iff_false _).mp (hgraph ▸ hxy)).elim
      · exact ⟨fun _ _ h1 _ => ((Set.mem_empty_iff_false _).mp (hgraph ▸ h1)).elim,
               fun _ h1 _ _ => ((Set.mem_empty_iff_false _).mp (hgraph ▸ h1)).elim⟩
    · exact Or.inr (fun w hw => by
        rcases evalWord_result_mem_or_eq p.toCondition w c d hw with heq | hmem
        · exact hdc heq
        · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
          exact hm.elim (hd_fresh m).1 (hd_fresh m).2)
  -- Work directly with the toExtension witness (avoids set/obtain opacity issues)
  -- h1graph: graph of (p.seq n extended by (c,d)) = ∅ ∪ {(c,d)} = resolved via spec
  have h1graph : (h1can.toExtension.toKnightCondition.seq n).graph =
      (p.seq n).graph ∪ {(c, d)} := by
    -- simp unfolds CanExtend.toExtension and reduces if n=n to expose spec
    simp only [CanExtend.toExtension, ite_true]
    exact h1can.toCanExtendFPA.toExtension.spec
  have h1le : h1can.toExtension.toKnightCondition ≤ p := by
    intro m
    by_cases hm : m = n
    · subst hm; rw [h1graph]; exact Set.subset_union_left
    · -- unfold seq and reduce if m≠n to get (p.seq m).graph ⊆ (p.seq m).graph
      simp only [CanExtend.toExtension, if_neg hm]; exact le_refl _
  have h1mem : (c, d) ∈ (h1can.toExtension.toKnightCondition.seq n).graph :=
    h1graph ▸ Set.mem_union_right _ (Set.mem_singleton _)
  -- Every point in the extended graph is (c, d) (empty base + spec)
  have h1spec : ∀ point ∈ (h1can.toExtension.toKnightCondition.seq n).graph,
      point = (c, d) := fun point hp => by
    rcases h1can.toExtension.spec n point hp with h | ⟨-, rfl⟩
    · rw [hgraph] at h; exact ((Set.mem_empty_iff_false _).mp h).elim
    · rfl
  -- Second extension: add (a, a) at index n
  have h2can : h1can.toExtension.toKnightCondition.CanExtend n a a := by
    refine { toCanExtendFPA := ?_, noNewCycles := Or.inl rfl }
    refine { freshDom := ?_, freshRan := ?_, orderCompat := ?_, fixingCompat := ?_ }
    · -- a ∉ dom; only c is in dom (via h1spec) and a ≠ c
      exact fun ⟨_, hx⟩ => by
        have := h1spec _ hx; simp only [Prod.mk.injEq] at this
        exact absurd this.1 (ne_of_lt (lt_trans habc hbc))
    · -- a ∉ ran; only d is in ran (via h1spec) and a < d
      exact fun ⟨_, hx⟩ => by
        have := h1spec _ hx; simp only [Prod.mk.injEq] at this
        exact absurd this.2 (ne_of_lt hda)
    · -- orderCompat: only pair is (c, d); c > b > a and d > a, so both sides false
      exact fun ⟨x, y⟩ hxy => by
        have := h1spec _ hxy; simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact iff_of_false (not_le.mpr (lt_trans habc hbc)) (not_le.mpr hda)
    · constructor
      · -- a = a → ∀ q ∈ graph, q.1 ≤ a → q.1 = q.2; vacuous since c > a
        exact fun _ ⟨x, y⟩ hxy hxa => by
          have := h1spec _ hxy; simp only [Prod.mk.injEq] at this
          obtain ⟨rfl, -⟩ := this
          exact absurd hxa (not_le.mpr (lt_trans habc hbc))
      · exact fun _ _ _ _ => rfl
  obtain ⟨p₂, h2le, h2mem⟩ := h2can.exists_extension
  -- (c, d) is also in p₂.seq n (graphs grow: p₂ ≤ p₁ means p₁'s graphs ⊆ p₂'s)
  have hcd_mem : (c, d) ∈ (p₂.seq n).graph := h2le n h1mem
  -- The word [(n, false)] fixes a and sends c to d < b
  refine ⟨p₂, le_trans h2le h1le, [(n, false)], ?_, d, ?_, hdb⟩
  · -- evalWord p₂ [(n, false)] a = some a
    simp [evalWord, evalLetter, PartialInj.apply?_of_mem h2mem]
  · -- evalWord p₂ [(n, false)] c = some d
    simp [evalWord, evalLetter, PartialInj.apply?_of_mem hcd_mem]

end KnightCondition
