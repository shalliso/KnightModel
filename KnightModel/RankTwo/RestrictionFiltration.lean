import KnightModel.RankTwo.Restriction

/-! # A wide collection of charts gives a tree of countable restrictions

We present a tree by its levels and its coherent predecessor maps. On an
ordinal index this is the usual tree ordered by restriction: each node on
a higher level has exactly one predecessor at each smaller level.
-/

namespace KnightModel.RankTwo.Restriction

/-- The unary colors and binary comparison data recorded by an endpoint. -/
structure Chart (X : Type u) where
  color : X → Nat
  rel : X → X → Prop

def Chart.comap (C : Chart X) (f : Y → X) : Chart Y :=
  ⟨C.color ∘ f, fun x y => C.rel (f x) (f y)⟩

theorem Chart.eq_of_agreement (C D : Chart X) (color : ∀ x, C.color x = D.color x)
    (rel : ∀ x y, C.rel x y ↔ D.rel x y) : C = D := by
  cases C
  cases D
  congr
  · exact funext color
  · exact funext (fun x => funext (fun y => propext (rel x y)))

/-- Increasing pieces exhausting the domain on which the chart rows differ. -/
structure Filtration (S : Stages ι) (X : Type u) where
  mem : ι → X → Prop
  mono : ∀ {i j}, S.le i j → ∀ {x}, mem i x → mem j x
  exhaustive : ∀ x, ∃ i, mem i x

/-- Countable levels with coherent restrictions and a specified injective
family of cofinal branches. With indices ω₁ and family size ℵ₂ this is a
Kurepa tree written in level notation. -/
structure CountableLevelTree (S : Stages ι) (B : Type u) where
  node : ι → Type v
  down : ∀ {i j}, S.le i j → node j → node i
  down_refl : ∀ i (x : node i), down (S.refl i) x = x
  down_trans : ∀ {i j k} (hij : S.le i j) (hjk : S.le j k) (x : node k),
    down hij (down hjk x) = down (S.trans hij hjk) x
  countable : ∀ i, CountablyCovered (fun _ : node i => True)
  branch : B → ∀ i, node i
  coherent : ∀ b {i j} (h : S.le i j), down h (branch b j) = branch b i
  separates : ∀ b c, (∀ i, branch b i = branch c i) → b = c

namespace Filtration

variable {ι : Type u} {X : Type v} {B : Type w} {S : Stages ι} (F : Filtration S X)

abbrev Piece (i : ι) := {x // F.mem i x}

/-- Restrict a chart to the domain present at a given level. -/
def trace (C : Chart X) (i : ι) : Chart (F.Piece i) := C.comap Subtype.val

abbrev Level (e : B → Chart X) (i : ι) :=
  { t : Chart (F.Piece i) // ∃ b, t = F.trace (e b) i }

def restrictNode (e : B → Chart X) {i j : ι} (h : S.le i j) (t : F.Level e j) :
    F.Level e i := by
  let incl (x : F.Piece i) : F.Piece j := ⟨x.val, F.mono h x.property⟩
  refine ⟨t.val.comap incl, ?_⟩
  obtain ⟨b, hb⟩ := t.property
  exact ⟨b, by rw [hb]; rfl⟩

/-- Distinct rows give distinct full branches; joint coverage of two
coordinates is what detects a difference in their binary relation. -/
noncomputable def treeOfTraces [Nonempty B] (e : B → Chart X)
    (inj : ∀ b c, e b = e c → b = c)
    (small : ∀ i, CountablyCovered (fun t => ∃ b, t = F.trace (e b) i)) :
    CountableLevelTree S B where
  node := F.Level e
  down := F.restrictNode e
  down_refl := fun _ _ => rfl
  down_trans := fun _ _ _ => rfl
  countable := by
    classical
    intro i
    obtain ⟨f, hf⟩ := small i
    let base : F.Level e i := ⟨F.trace (e (Classical.choice (inferInstance : Nonempty B))) i, _, rfl⟩
    let g (n : Nat) : F.Level e i :=
      if h : ∃ b, f n = F.trace (e b) i then ⟨f n, h⟩ else base
    refine ⟨g, fun t _ => ?_⟩
    obtain ⟨n, hn⟩ := hf t.val t.property
    have h : ∃ b, f n = F.trace (e b) i := hn ▸ t.property
    exact ⟨n, Subtype.ext (by simpa [g, h] using hn)⟩
  branch b i := ⟨F.trace (e b) i, b, rfl⟩
  coherent := fun _ {_ _} _ => rfl
  separates := by
    intro b c h
    apply inj
    apply Chart.eq_of_agreement
    · intro x
      obtain ⟨i, hx⟩ := F.exhaustive x
      exact congrArg (fun t : F.Level e i => t.val.color ⟨x, hx⟩) (h i)
    · intro x y
      obtain ⟨i, hx⟩ := F.exhaustive x
      obtain ⟨j, hy⟩ := F.exhaustive y
      obtain ⟨k, hk⟩ := S.bounded (fun n => if n = 0 then i else j)
      have hxk := F.mono (show S.le i k by simpa using hk 0) hx
      have hyk := F.mono (show S.le j k by simpa using hk 1) hy
      exact iff_of_eq (congrArg (fun t : F.Level e k => t.val.rel ⟨x, hxk⟩ ⟨y, hyk⟩) (h k))

end Filtration
end KnightModel.RankTwo.Restriction
