import KnightModel.RankTwo.ScottFrames

/-! # The language of frames

Besides the base relations, the language has the frame sort, comparison of images
and each parameterized transition relation. When working below an anchor, all
these tests reduce to equalities of coordinates, existence of a right factor, and
evaluation of the named program. In particular the atomic hypothesis in the
general moving-anchor lemma can be discharged without assuming a partial
isomorphism on the frame sorts.
-/

namespace KnightModel.RankTwo.Scott

universe u v

inductive FrameRelation (B : Nat → Type u) (K : Nat → Type v) : Nat → Type (max u v) where
  | base {n} (r : B n) : FrameRelation B K n
  | frame : FrameRelation B K 1
  | below : FrameRelation B K 2
  | transition {n} (k : K n) : FrameRelation B K (n+2)

variable {PL PR CL FL CR FR : Type _} {L : FrameAction CL FL} {R : FrameAction CR FR}
variable {B : Nat → Type u} {K : Nat → Type v}

structure FrameInterpretation (B : Nat → Type u) (K : Nat → Type v)
    (P : Type _) {C F : Type _} (A : FrameAction C F) where
  faithful : ∀ f c d, A.act f c = A.act f d → c = d
  base : Model B P
  run : ∀ {n}, K n → Tuple P n → Option C

namespace FrameInterpretation

variable {P C F : Type _} {A : FrameAction C F}

def model (I : FrameInterpretation B K P A) : Model (FrameRelation B K) (P ⊕ F)
  | _, .base r, s => ∃ t, (∀ i, s i = .inl (t i)) ∧ I.base r t
  | _, .frame, s => ∃ f, s 0 = .inr f
  | _, .below, s => ∃ v h, s 0 = .inr (A.act v h) ∧ s 1 = .inr v
  | _, .transition k, s => ∃ t h v, (∀ i, s i.succ.succ = .inl (t i)) ∧
    I.run k t = some h ∧ s 0 = .inr (A.act v h) ∧ s 1 = .inr v

/-- Faithfulness lets one cancel the enclosing anchor from all atomic tests. -/
theorem read_injective (I : FrameInterpretation B K P A) (u : F) {c d : P ⊕ C}
    (h : A.read u c = A.read u d) : c = d := by
  cases c <;> cases d
  case inl.inl => exact congrArg Sum.inl (Sum.inl.inj h)
  case inr.inr => exact congrArg Sum.inr (I.faithful _ _ _ (Sum.inr.inj h))
  all_goals cases h

private theorem read_eq_inl {u : F} {c : P ⊕ C} {p : P} :
    A.read u c = .inl p ↔ c = .inl p := by cases c <;> simp [FrameAction.read]

private theorem read_eq_inr {u : F} {c : P ⊕ C} {f : F} :
    A.read u c = .inr f ↔ ∃ d, c = .inr d ∧ A.act u d = f := by
  cases c <;> simp [FrameAction.read]

def tests (I : FrameInterpretation B K P A) : Model (FrameRelation B K) (P ⊕ C)
  | _, .base r, s => ∃ t, (∀ i, s i = .inl (t i)) ∧ I.base r t
  | _, .frame, s => ∃ c, s 0 = .inr c
  | _, .below, s => ∃ d h, s 0 = .inr (A.comp d h) ∧ s 1 = .inr d
  | _, .transition k, s => ∃ t h d, (∀ i, s i.succ.succ = .inl (t i)) ∧
    I.run k t = some h ∧ s 0 = .inr (A.comp d h) ∧ s 1 = .inr d

theorem model_read (I : FrameInterpretation B K P A) (u : F) {n}
    (r : FrameRelation B K n) (s : Tuple (P ⊕ C) n) :
    I.model r (A.read u ∘ s) ↔ I.tests r s := by
  cases r with
  | base => simp only [model, tests, Function.comp_apply, read_eq_inl]
  | frame => exact ⟨fun ⟨_, h⟩ => by obtain ⟨c, hc, _⟩ := read_eq_inr.mp h; exact ⟨c, hc⟩,
                     fun ⟨c, hc⟩ => ⟨A.act u c, congrArg (A.read u) hc⟩⟩
  | below =>
    constructor
    · rintro ⟨v, h, a, b⟩
      obtain ⟨d, hd, rfl⟩ := read_eq_inr.mp b
      refine ⟨d, h, I.read_injective u ?_, hd⟩
      exact a.trans (congrArg Sum.inr (A.act_comp _ _ _).symm)
    · rintro ⟨d, h, a, b⟩
      exact ⟨A.act u d, h, (congrArg (A.read u) a).trans
        (congrArg Sum.inr (A.act_comp _ _ _)), congrArg (A.read u) b⟩
  | transition k =>
    constructor
    · rintro ⟨t, h, v, pt, ev, a, b⟩
      obtain ⟨d, hd, rfl⟩ := read_eq_inr.mp b
      refine ⟨t, h, d, fun i => read_eq_inl.mp (pt i), ev, I.read_injective u ?_, hd⟩
      exact a.trans (congrArg Sum.inr (A.act_comp _ _ _).symm)
    · rintro ⟨t, h, d, pt, ev, a, b⟩
      exact ⟨t, h, A.act u d, fun i => read_eq_inl.mpr (pt i), ev,
        (congrArg (A.read u) a).trans (congrArg Sum.inr (A.act_comp _ _ _)),
        congrArg (A.read u) b⟩

end FrameInterpretation

namespace CoordinateMatches

variable {G : CoordinateMatches PL PR L R}
variable {I : FrameInterpretation B K PL L} {J : FrameInterpretation B K PR R}

/-- All conditions here concern base data or program coordinates. -/
structure Interprets (G : CoordinateMatches PL PR L R)
    (I : FrameInterpretation B K PL L) (J : FrameInterpretation B K PR R) : Prop where
  param_eq : ∀ {p a b c d}, G.param p a b → G.param p c d → (a = c ↔ b = d)
  code_eq : ∀ {p a b c d}, G.code p a b → G.code p c d → (a = c ↔ b = d)
  base : ∀ {p n} (r : B n) {s t}, (∀ i, G.param p (s i) (t i)) → (I.base r s ↔ J.base r t)
  run : ∀ {p n} (k : K n) {s t}, (∀ i, G.param p (s i) (t i)) →
    Option.Rel (G.code p) (I.run k s) (J.run k t)

private theorem paramTuple {n} {p : G.State} {a : Tuple (PL ⊕ CL) n} {b : Tuple (PR ⊕ CR) n}
    (s : Tuple PL n) (same : ∀ i, G.same p (a i) (b i)) (h : ∀ i, a i = .inl (s i)) :
    ∃ t : Tuple PR n, (∀ i, b i = .inl (t i)) ∧ ∀ i, G.param p (s i) (t i) := by
  classical
  have one (i : Fin n) : ∃ t, b i = .inl t ∧ G.param p (s i) t := by
    have m := same i
    rw [h i] at m
    cases e : b i with
    | inl v => rw [e] at m; exact ⟨v, rfl, m⟩
    | inr v => rw [e] at m; exact False.elim m
  exact ⟨fun i => (one i).choose, fun i => (one i).choose_spec.1, fun i => (one i).choose_spec.2⟩

private theorem codeOne {p : G.State} {a b} {c : CL} (m : G.same p a b) (h : a = .inr c) :
    ∃ d, b = .inr d ∧ G.code p c d := by
  subst a
  cases b with
  | inl v => exact False.elim m
  | inr d => exact ⟨d, rfl, m⟩

/-- Swap the sides, retaining exactly the same index-state witnesses. -/
def swap (G : CoordinateMatches PL PR L R) : CoordinateMatches PR PL R L where
  State := G.State
  param p b a := G.param p a b
  code p d c := G.code p c d
  one := G.one
  comp := fun m n => G.comp m n
  proper := fun h => (G.proper h).symm
  refines := G.refines
  keepParam := fun h _ _ m => G.keepParam h m
  keepCode := fun h _ _ m => G.keepCode h m
  paramForth := G.paramBack
  paramBack := G.paramForth
  codeForth := G.codeBack
  codeBack := G.codeForth

private theorem optionRel_flip {α β : Type _} {r : α → β → Prop} {x : Option α} {y : Option β}
    (h : Option.Rel r x y) : Option.Rel (fun b a => r a b) y x := by
  cases h with
  | none => exact .none
  | some h => exact .some h

private theorem Interprets.swap (H : G.Interprets I J) : G.swap.Interprets J I where
  param_eq := fun m h => (H.param_eq m h).symm
  code_eq := fun m h => (H.code_eq m h).symm
  base := fun r _ _ m => (H.base r m).symm
  run := by
    intro p n k s t m
    exact optionRel_flip (H.run k m)

private theorem tests_mp (H : G.Interprets I J) {p : G.State} {n}
    (r : FrameRelation B K n) {a : Tuple (PL ⊕ CL) n} {b : Tuple (PR ⊕ CR) n}
    (m : ∀ i, G.same p (a i) (b i)) (ha : I.tests r a) : J.tests r b := by
  cases r with
  | base r =>
    obtain ⟨s, hs, hr⟩ := ha
    obtain ⟨t, ht, eq⟩ := paramTuple s m hs
    exact ⟨t, ht, (H.base r eq).mp hr⟩
  | frame =>
    obtain ⟨c, hc⟩ := ha
    obtain ⟨d, hd, _⟩ := codeOne (m 0) hc
    exact ⟨d, hd⟩
  | below =>
    obtain ⟨d, h, h₀, h₁⟩ := ha
    obtain ⟨d', hd, eqd⟩ := codeOne (m 1) h₁
    obtain ⟨z, hz, eqz⟩ := codeOne (m 0) h₀
    obtain ⟨q, k, e, eqh⟩ := G.codeForth p h
    have ecz := H.code_eq (G.keepCode e eqz) (G.comp (G.keepCode e eqd) eqh)
    exact ⟨d', k, hz.trans (congrArg Sum.inr (ecz.mp rfl)), hd⟩
  | transition k =>
    obtain ⟨s, hs, d, hp, ev, h₀, h₁⟩ := ha
    obtain ⟨t, ht, pm⟩ := paramTuple s (fun i => m i.succ.succ) hp
    obtain ⟨d', hd, eqd⟩ := codeOne (m 1) h₁
    obtain ⟨z, hz, eqz⟩ := codeOne (m 0) h₀
    have run := H.run k pm
    rw [ev] at run
    cases e : J.run k t with
    | none => rw [e] at run; cases run
    | some h' =>
      rw [e] at run
      obtain ⟨eqh⟩ := run
      exact ⟨t, h', d', ht, e, hz.trans (congrArg Sum.inr
        ((H.code_eq eqz (G.comp eqd eqh)).mp rfl)), hd⟩

theorem Interprets.tests_iff (H : G.Interprets I J) {p : G.State} {n}
    (r : FrameRelation B K n) {a : Tuple (PL ⊕ CL) n} {b : Tuple (PR ⊕ CR) n}
    (m : ∀ i, G.same p (a i) (b i)) : I.tests r a ↔ J.tests r b := by
  refine ⟨tests_mp H r m, tests_mp H.swap (p := p) r ?_⟩
  intro i
  have h := m i
  cases ea : a i <;> cases eb : b i <;> rw [ea, eb] at h <;> exact h

private theorem same_eq (H : G.Interprets I J) {p} {a c : PL ⊕ CL} {b d : PR ⊕ CR}
    (h : G.same p a b) (k : G.same p c d) : a = c ↔ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [same, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h k ⊢ <;>
    first | exact False.elim h | exact False.elim k | exact Iff.rfl |
      exact H.param_eq h k | exact H.code_eq h k

theorem Interprets.atoms (H : G.Interprets I J) (p : G.State) (u : FL) (v : FR) {n}
    (a : Tuple (PL ⊕ CL) n) (b : Tuple (PR ⊕ CR) n) (m : ∀ i, G.same p (a i) (b i))
    (r : Atom (FrameRelation B K) n) :
    r.Holds I.model (L.read u ∘ a) ↔ r.Holds J.model (R.read v ∘ b) := by
  cases r with
  | eq i j =>
    have hh := same_eq H (m i) (m j)
    exact ⟨fun e => congrArg (R.read v) (hh.mp (I.read_injective u e)),
           fun e => congrArg (L.read u) (hh.mpr (J.read_injective v e))⟩
  | rel r f =>
    exact (I.model_read u r (a ∘ f)).trans
      ((H.tests_iff r (fun i => m (f i))).trans (J.model_read v r (b ∘ f)).symm)

/-- The large frame structure satisfies the actual Scott sentence of its countable
counterpart whenever the finite coordinate interpretations and atlas laws hold. -/
theorem Interprets.satisfies (H : G.Interprets I J) (C : Presentation (FrameRelation B K) (PL ⊕ FL))
    (p : G.State) (u : FL) (v : FR) :
    BackAndForth.Satisfies J.model (C.sentence I.model) :=
  (C.satisfies_iff_backAndForth _ _).mpr
    ⟨G.system I.model J.model H.atoms, ⟨G.empty p u v⟩⟩

end CoordinateMatches
end KnightModel.RankTwo.Scott
