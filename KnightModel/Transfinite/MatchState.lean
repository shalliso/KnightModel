import KnightModel.RankTwo.Scott
import KnightModel.PartialIso
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Basic

/-! # Finite records for back-and-forth on an arbitrary ordered base -/

namespace KnightModel.Transfinite

open RankTwo.Scott

variable {R : ℕ → Type} {I J : Type} [LinearOrder I] [LinearOrder J]
variable {D : Model R I} {E : Model R J}

/-- An ordinary old-model back-and-forth which also preserves the given index order. -/
structure OrderedBF (D : Model R I) (E : Model R J) extends BackAndForth D E where
  order : ∀ {n} {s : Tuple I n} {t : Tuple J n}, matchTuples s t →
    ∀ a b, s a ≤ s b ↔ t a ≤ t b

namespace OrderedBF

def ofNamed (F : BackAndForth D E) (r : R 2)
    (l : ∀ s, D r s ↔ s 0 ≤ s 1) (v : ∀ t, E r t ↔ t 0 ≤ t 1) : OrderedBF D E where
  toBackAndForth := F
  order := by
    intro n s t h a b
    let k : Fin 2 → Fin n := Fin.cases a (fun _ => b)
    exact (l (s ∘ k)).symm.trans ((F.atoms h (.rel r k)).trans (v (t ∘ k)))

def flip (F : OrderedBF D E) : OrderedBF E D where
  matchTuples s t := F.matchTuples t s
  atoms h a := (F.atoms h a).symm
  forth h := F.back h
  back h := F.forth h
  order h a b := (F.order h a b).symm

/-- A record stores the actual old tuple match, including any dependencies of
which the index reduct is unaware. -/
structure State (F : OrderedBF D E) where
  arity : ℕ
  left : Tuple I arity
  right : Tuple J arity
  ok : F.matchTuples left right

end OrderedBF

namespace OrderedBF.State

variable {F : OrderedBF D E}

def graph (p : F.State) : Set (I × J) := Set.range fun a => (p.left a,p.right a)
def dom (p : F.State) : Set I := {x | ∃ y, (x,y) ∈ p.graph}
def ran (p : F.State) : Set J := {y | ∃ x, (x,y) ∈ p.graph}

instance : Preorder F.State where
  le q p := p.graph ⊆ q.graph
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ h k := k.trans h

theorem mem_ran_iff {p : F.State} {y : J} : y ∈ p.ran ↔ ∃ x, (x,y) ∈ p.graph := Iff.rfl

theorem finite_ran (p : F.State) : p.ran.Finite := Set.Finite.subset (Set.finite_range p.right) (by
  rintro _ ⟨_,a,e⟩
  exact ⟨a,congrArg Prod.snd e⟩)

theorem functional (p : F.State) : ∀ a ∈ p.graph, ∀ b ∈ p.graph, a.1 = b.1 → a.2 = b.2 := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ h
  exact (F.atoms p.ok (.eq i j)).mp h

theorem injective (p : F.State) : ∀ a ∈ p.graph, ∀ b ∈ p.graph, a.2 = b.2 → a.1 = b.1 := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ h
  exact (F.atoms p.ok (.eq i j)).mpr h

def toPartialIso (p : F.State) : PartialIso I J where
  graph := p.graph
  functional := p.functional
  injective := p.injective
  order_pres := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ h
    exact (F.order p.ok i j).mp h

def symm (p : F.State) : F.flip.State := ⟨p.arity,p.right,p.left,p.ok⟩

@[simp] theorem symm_symm (p : F.State) : p.symm.symm = p := rfl

theorem mem_symm_graph {p : F.State} {i : I} {j : J} : (j,i) ∈ p.symm.graph ↔ (i, j) ∈ p.graph := by
  constructor <;> rintro ⟨a,e⟩ <;> exact ⟨a,congrArg Prod.swap e⟩

theorem mem_dom_symm_iff_mem_ran (p : F.State) {j : J} : j ∈ p.symm.dom ↔ j ∈ p.ran :=
  exists_congr fun _ => mem_symm_graph

/-- Turn an extension on the reversed base into an extension of the original record. -/
theorem reverse_refines {p : F.State} {q : F.flip.State} (h : q ≤ p.symm) : q.symm ≤ p :=
  fun _ pair => mem_symm_graph.mpr (h (mem_symm_graph.mpr pair))

theorem extendIndexLeft (p : F.State) (x : I) :
    ∃ (q : F.State) (y : J), q ≤ p ∧ (x, y) ∈ q.graph := by
  obtain ⟨y,h⟩ := F.forth p.ok x
  let q : F.State := ⟨p.arity+1,push x p.left,push y p.right,h⟩
  exact ⟨q,y,fun _ ⟨a,e⟩ => ⟨a.succ,e⟩,0,rfl⟩

theorem extendIndexRight (p : F.State) (y : J) :
    ∃ (q : F.State) (x : I), q ≤ p ∧ (x, y) ∈ q.graph := by
  obtain ⟨x,h⟩ := F.back p.ok y
  let q : F.State := ⟨p.arity+1,push x p.left,push y p.right,h⟩
  exact ⟨q,x,fun _ ⟨a,e⟩ => ⟨a.succ,e⟩,0,rfl⟩

theorem relation (p : F.State) {n} (r : R n) {s : Tuple I n} {t : Tuple J n}
    (h : ∀ a, (s a, t a) ∈ p.graph) : D r s ↔ E r t := by
  choose f eq using h
  have l : p.left ∘ f = s := funext fun a => congrArg Prod.fst (eq a)
  have v : p.right ∘ f = t := funext fun a => congrArg Prod.snd (eq a)
  have equiv := F.atoms p.ok (.rel r f)
  change D r (p.left ∘ f) ↔ E r (p.right ∘ f) at equiv
  rwa [l,v] at equiv

end OrderedBF.State
end KnightModel.Transfinite
