/-! # Stabilization of rank-one orbit partitions

In a relative Scott orbit of comparison rank one, countably many orbital
functions compare any two points. Increasing the parameter set refines the
orbit partitions and all the orbital functions preserve these partitions.
The equivalence relations below describe the resulting labels. They need
not be orbits of any one group acting on the uncountable model.

The only property of the first uncountable ordinal used in stabilization is
that any countable sequence of stages has an upper bound.
-/

namespace KnightModel.RankTwo.Restriction

/-- A preorder of stages in which every countable sequence has an upper bound. -/
structure Stages (ι : Type u) where
  start : ι
  le : ι → ι → Prop
  refl : ∀ i, le i i
  trans : ∀ {i j k}, le i j → le j k → le i k
  bounded : ∀ f : Nat → ι, ∃ i, ∀ n, le (f n) i

/-- A countable cover is allowed to enumerate some points outside the set. -/
def CountablyCovered (p : X → Prop) : Prop :=
  ∃ f : Nat → X, ∀ x, p x → ∃ n, f n = x

/-- The countable-fiber and comparison alternatives for rank one. The comparison
functions act on one relative orbit and preserve every later orbit partition. -/
def RankOne (E : ι → Setoid X) : Prop :=
  CountablyCovered (fun _ : X => True) ∨ ∃ f : Nat → X → X,
    (∀ x y, (∃ n, x = f n y) ∨ (∃ n, y = f n x)) ∧
    (∀ i n x y, (E i).r x y → (E i).r (f n x) (f n y))

/-- Countably many decreasing truth values have a common stabilization stage. -/
private theorem simultaneous (S : Stages ι) (P : ι → Nat → Prop)
    (refine : ∀ i j, S.le i j → ∀ n, P j n → P i n) :
    ∃ i, ∀ j, S.le i j → ∀ n, P i n ↔ P j n := by
  classical
  let w (n : Nat) : ι :=
    if h : ∃ i, ¬ P i n then h.choose else S.start
  obtain ⟨i, hi⟩ := S.bounded w
  refine ⟨i, fun j hij n => ⟨?_, refine i j hij n⟩⟩
  intro hin
  apply Classical.byContradiction
  intro hjn
  have h : ∃ k, ¬ P k n := ⟨j, hjn⟩
  have hw : ¬ P (w n) n := by simpa [w, h] using h.choose_spec
  exact hw (refine _ _ (hi n) n hin)

private theorem commonStage (S : Stages ι) (i j : ι) :
    ∃ k, S.le i k ∧ S.le j k := by
  obtain ⟨k, hk⟩ := S.bounded (fun n => if n = 0 then i else j)
  exact ⟨k, by simpa using hk 0, by simpa using hk 1⟩

private theorem stabilize_small (S : Stages ι) (P : ι → X → Prop)
    (refine : ∀ i j, S.le i j → ∀ x, P j x → P i x)
    (k : ι) (small : CountablyCovered (P k)) :
    ∃ i, ∀ j, S.le i j → ∀ x, P i x ↔ P j x := by
  obtain ⟨f, cover⟩ := small
  obtain ⟨l, hl⟩ := simultaneous S (fun i n => P i (f n))
    (fun i j hij n => refine i j hij (f n))
  obtain ⟨i, hki, hli⟩ := commonStage S k l
  refine ⟨i, fun j hij x => ⟨?_, refine i j hij x⟩⟩
  intro hx
  obtain ⟨n, rfl⟩ := cover x (refine _ _ hki _ hx)
  exact (hl j (S.trans hli hij) n).mp (refine _ _ hli _ hx)

/-- A cell of a rank-one point stabilizes under countably directed refinements. -/
theorem rankOne_cell_stabilizes (S : Stages ι) (E : ι → Setoid X)
    (refine : ∀ i j, S.le i j → ∀ x y, (E j).r x y → (E i).r x y)
    (low : RankOne E) (a : X) :
    ∃ i, ∀ j, S.le i j → ∀ x, (E i).r x a ↔ (E j).r x a := by
  classical
  by_cases small : ∃ k, CountablyCovered (fun x => (E k).r x a)
  · obtain ⟨k, hk⟩ := small
    exact stabilize_small S (fun i x => (E i).r x a) (fun i j h x => refine i j h x a) k hk
  rcases low with ⟨g, hg⟩ | ⟨f, compare, congr⟩
  · exact (small ⟨S.start, g, fun x _ => hg x trivial⟩).elim
  -- Every cell meets the same countable transversal, the orbit functions at a.
  have hits (i : ι) (z : X) : ∃ n, (E i).r z (f n a) := by
    apply Classical.byContradiction
    intro noHit
    apply small
    refine ⟨i, fun n => f n z, ?_⟩
    intro x hxa
    rcases compare z x with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact (noHit ⟨n, hn ▸ congr i n x a hxa⟩).elim
    · exact ⟨n, hn.symm⟩
  have stage (m : Nat) := simultaneous S
    (fun i n => (E i).r (f m a) (f n a)) (fun i j h _ => refine i j h _ _)
  obtain ⟨i, hi⟩ := S.bounded (fun m => (stage m).choose)
  refine ⟨i, fun j hij x => ⟨?_, refine i j hij x a⟩⟩
  intro hxa
  obtain ⟨m, hm⟩ := hits j x
  obtain ⟨n, hn⟩ := hits j a
  have hmn := (E i).iseqv.trans ((E i).iseqv.symm (refine i j hij _ _ hm))
    ((E i).iseqv.trans hxa (refine i j hij _ _ hn))
  have hmn' := refine _ _ (hi m) _ _ hmn
  exact (E j).iseqv.trans hm ((E j).iseqv.trans
    (((stage m).choose_spec j (S.trans (hi m) hij) n).mp hmn') ((E j).iseqv.symm hn))

/-- The possible first coordinates over a fixed tuple in the ambient partition. -/
def HeadOrbit (A : Setoid (List X)) (u : List X) (a : X) :=
  { x : X // A.r (x :: u) (a :: u) }

private def headPartition (A E : Setoid (List X)) (u : List X) (a : X) :
    Setoid (HeadOrbit A u a) where
  r x y := E.r (x.val :: u) (y.val :: u)
  iseqv := {
    refl := fun _ => E.iseqv.refl _
    symm := E.iseqv.symm
    trans := E.iseqv.trans }

/-- A chain of partitions on finite tuples with the projection and extension
properties of finite Scott orbit labels. `liftHead` transfers just one point;
no automorphism of the large structure is assumed. -/
structure TuplePartitions (S : Stages ι) (X : Type v) where
  ambient : Setoid (List X)
  atStage : ι → Setoid (List X)
  refinesAmbient : ∀ i x y, (atStage i).r x y → ambient.r x y
  refine : ∀ i j, S.le i j → ∀ x y, (atStage j).r x y → (atStage i).r x y
  length_eq : ∀ i x y, (atStage i).r x y → x.length = y.length
  forgetHead : ∀ i a b u v, (atStage i).r (a :: u) (b :: v) → (atStage i).r u v
  liftHead : ∀ i u v, (atStage i).r u v → ∀ a, ∃ b, (atStage i).r (a :: u) (b :: v)

/-- Rank one for a point at the indicated finite base, with all stages refining
the ambient partition. The fiber contains only points with the given base label. -/
def TuplePartitions.lowOver {S : Stages ι} (T : TuplePartitions S X) (u : List X) (a : X) :
    Prop := RankOne (fun i => headPartition T.ambient (T.atStage i) u a)

/-- Finite-tuples stabilization from rank one for each new entry over its tail. -/
theorem tuple_cell_stabilizes (S : Stages ι) (T : TuplePartitions S X) (good : X → Prop)
    (low : ∀ a, good a → ∀ u, (∀ x ∈ u, good x) → T.lowOver u a)
    (u : List X) (hu : ∀ x ∈ u, good x) :
    ∃ i, ∀ j, S.le i j → ∀ v, (T.atStage i).r v u ↔ (T.atStage j).r v u := by
  induction u with
  | nil =>
    refine ⟨S.start, fun j hij v => ⟨?_, T.refine _ _ hij _ _⟩⟩
    intro hv
    have hv0 : v = [] := List.length_eq_zero_iff.mp (T.length_eq _ _ _ hv)
    exact hv0 ▸ (T.atStage j).iseqv.refl []
  | cons a u ih =>
    have hgood : ∀ x ∈ u, good x := fun x hx => hu x (List.mem_cons_of_mem a hx)
    obtain ⟨l, hl⟩ := ih hgood
    let a₀ : HeadOrbit T.ambient u a := ⟨a, T.ambient.iseqv.refl _⟩
    obtain ⟨m, hm⟩ := rankOne_cell_stabilizes S
      (fun k => headPartition T.ambient (T.atStage k) u a)
      (fun i j h x y => T.refine i j h _ _) (low a (hu a (by simp)) u hgood) a₀
    obtain ⟨i, hli, hmi⟩ := commonStage S l m
    refine ⟨i, fun j hij v => ⟨?_, T.refine i j hij _ _⟩⟩
    intro h
    cases v with
    | nil => simpa using T.length_eq _ _ _ h
    | cons b v =>
      have hv := T.forgetHead i b a v u h
      have hvj := (hl j (S.trans hli hij) v).mp (T.refine l i hli _ _ hv)
      obtain ⟨c, hbc⟩ := T.liftHead j v u hvj b
      have hca := (T.atStage i).iseqv.trans ((T.atStage i).iseqv.symm
        (T.refine i j hij _ _ hbc)) h
      let c₀ : HeadOrbit T.ambient u a := ⟨c, T.refinesAmbient i _ _ hca⟩
      have hca' := (hm j (S.trans hmi hij) c₀).mp (T.refine m i hmi _ _ hca)
      exact (T.atStage j).iseqv.trans hbc hca'

/-- All finite parameter lists drawn from a countable enumeration stabilize at
a common stage, at which a single endpoint label determines their joint profile.

`transport` is the one finite-tuple extension of an equal endpoint label.
`readout` says that equality of the stage partition preserves the joint label. -/
theorem countable_profile_factorization (S : Stages ι) (T : TuplePartitions S X)
    (good : X → Prop) (low : ∀ a, good a → ∀ u, (∀ x ∈ u, good x) → T.lowOver u a)
    (parameters : Nat → List X) (hparam : ∀ n x, x ∈ parameters n → good x)
    (label : ι → ι → Nat) (joint : ι → List X → Nat)
    (readout : ∀ k u v, (T.atStage k).r u v → joint k u = joint k v)
    (transport : ∀ i j k, S.le i j → S.le i k → label i j = label i k →
      ∀ u, ∃ v, (T.atStage i).r v u ∧ joint j u = joint k v) :
    ∃ i, ∀ j k, S.le i j → S.le i k → label i j = label i k →
      ∀ n, joint j (parameters n) = joint k (parameters n) := by
  classical
  have threshold (n : Nat) := tuple_cell_stabilizes S T good low (parameters n) (hparam n)
  obtain ⟨i, hi⟩ := S.bounded (fun n => (threshold n).choose)
  refine ⟨i, fun j k hij hik hlabel n => ?_⟩
  obtain ⟨v, hv, hvalue⟩ := transport i j k hij hik hlabel (parameters n)
  have hv' := T.refine _ _ (hi n) _ _ hv
  have hvk := ((threshold n).choose_spec k (S.trans (hi n) hik) v).mp hv'
  exact hvalue.trans (readout k _ _ hvk)

/-- A countable labeling of a tail, together with a countable initial part,
gives an explicit countable cover of all realized profiles. -/
theorem countable_range_of_tail_labels {Y : Type u} (S : Stages ι)
    (initial : ∀ i, CountablyCovered (fun j => ¬ S.le i j))
    (profile : ι → Y) (label : ι → ι → Nat)
    (tail : ∃ i, ∀ j k, S.le i j → S.le i k → label i j = label i k →
      profile j = profile k) :
    CountablyCovered (fun y => ∃ j, profile j = y) := by
  classical
  obtain ⟨i, htail⟩ := tail
  obtain ⟨left, hleft⟩ := initial i
  let right (n : Nat) : ι :=
    if h : ∃ j, S.le i j ∧ label i j = n then h.choose else i
  refine ⟨fun n => if n % 2 = 0 then profile (left (n / 2)) else profile (right (n / 2)), ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hij : S.le i j
  · let n := label i j
    have h : ∃ k, S.le i k ∧ label i k = n := ⟨j, hij, rfl⟩
    have hr : S.le i (right n) ∧ label i (right n) = n := by
      simpa [right, h] using h.choose_spec
    refine ⟨2 * n + 1, ?_⟩
    have hmod : (2 * n + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    simpa [hmod, hdiv] using htail (right n) j hr.1 hij hr.2
  · obtain ⟨n, hn⟩ := hleft j hij
    refine ⟨2 * n, ?_⟩
    have hmod : (2 * n) % 2 = 0 := by omega
    have hdiv : (2 * n) / 2 = n := by omega
    simp [hmod, hdiv, hn]

/-- The countable-restriction conclusion for a comparison chain whose initial
parts are countable (in particular for an omega-one chain). -/
theorem countable_joint_profiles (S : Stages ι) (T : TuplePartitions S X)
    (initial : ∀ i, CountablyCovered (fun j => ¬ S.le i j))
    (good : X → Prop) (low : ∀ a, good a → ∀ u, (∀ x ∈ u, good x) → T.lowOver u a)
    (parameters : Nat → List X) (hparam : ∀ n x, x ∈ parameters n → good x)
    (label : ι → ι → Nat) (joint : ι → List X → Nat)
    (readout : ∀ k u v, (T.atStage k).r u v → joint k u = joint k v)
    (transport : ∀ i j k, S.le i j → S.le i k → label i j = label i k →
      ∀ u, ∃ v, (T.atStage i).r v u ∧ joint j u = joint k v) :
    CountablyCovered (fun p : Nat → Nat => ∃ j, (fun n => joint j (parameters n)) = p) := by
  apply countable_range_of_tail_labels S initial _ label
  obtain ⟨i, hi⟩ := countable_profile_factorization S T good low parameters hparam label joint
    readout transport
  exact ⟨i, fun j k hij hik h => funext (hi j k hij hik h)⟩

end KnightModel.RankTwo.Restriction
