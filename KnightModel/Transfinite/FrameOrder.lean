import KnightModel.Transfinite.LexSignOrder
import KnightModel.RankTwo.ProgramDefinabilityComplete

/-! # The intrinsic linear order of the concrete proper frames -/

namespace KnightModel.Transfinite.FrameOrder

open RankTwo RankTwo.Semilinear RankTwo.Concrete LexSign

variable {I : Type} [LinearOrder I] (i : I)
local notation "V" => VectorGroup I
local notation "W" => Word (Letter I)
local notation "F" => SmallFrames i

/-- Invalid ambient words tie every pair of frames. -/
def point (f g : F) (w : List V) : Prop :=
  ∃ u : W, u.map Subtype.val = w ∧ f.val.val u < g.val.val u

private theorem word_unique {u v : W} (h : u.map Subtype.val = v.map Subtype.val) : u = v :=
  List.map_injective_iff.mpr Subtype.val_injective h

theorem point_map (f g : F) (u : W) :
    point i f g (u.map Subtype.val) ↔ f.val.val u < g.val.val u := by
  exact ⟨fun ⟨v,hv,h⟩ => word_unique hv ▸ h,fun h => ⟨u,rfl,h⟩⟩

private theorem point_laws (w : List V) : Laws (fun f g => point i f g w) := by
  by_cases h : ∃ u : W, u.map Subtype.val = w
  · obtain ⟨u,rfl⟩ := h
    simp only [point_map]
    exact ⟨lt_asymm,lt_trans,fun b h => (lt_or_ge _ _).imp_right (fun hb => hb.trans_lt h)⟩
  · have em (f g : F) : ¬point i f g w := fun ⟨u,hu,_⟩ => h ⟨u,hu⟩
    exact ⟨fun h => (em _ _ h).elim,fun h => (em _ _ h).elim,fun _ h => (em _ _ h).elim⟩

private abbrev raw (c : Code i) :=
  liftWordGraph (Subtype.val : Letter I → V) (fun x y => c.val x = y)

private theorem code_graph (c : Code i) : ∀ {k} (x y : List (Term V k)),
    Definable {p | raw i c (evalWord x p) (evalWord y p)} := by
  obtain ⟨n,⟨s,rfl⟩,p,hp⟩ := run_covers_vectors i c
  intro k x y
  have sem := all_scheme_definable i s (fun j => Term.const (p j)) x y
  convert sem using 1
  ext t
  change liftWordGraph _ _ _ _ ↔ liftWordGraph _ _ _ _
  simp only [liftWordGraph,eval_const_tuple,(run_vectors_iff i ⟨s,rfl⟩ p c).mp hp]

private theorem code_bound (c : Code i) :
    ∃ b : Nat, ∀ x y, raw i c x y → y.length ≤ x.length+b := by
  obtain ⟨n,k,p,hp⟩ := run_covers_vectors i c
  refine ⟨k.val.graphBound,?_⟩
  rintro x y ⟨u,v,rfl,rfl,h⟩
  have hs := (concrete_graph_bound i k p).sizes (((run_vectors_iff i k p c).mp hp _ _).mpr h)
  simpa using hs.2

private abbrev rawLT (x y : List V) : Prop := @LT.lt (Word V) inferInstance x y

private theorem point_test (f g : F) : WordTest (point i f g) := by
  obtain ⟨b,hb⟩ := code_bound i f.val
  obtain ⟨c,hc⟩ := code_bound i g.val
  let Q (x y : List V) := ∃ z, raw i g.val x z ∧ rawLT y z
  have ds : GraphDefinable (n:=0) (fun (_ : Fin 0 → V) => Q) :=
    GraphDefinable.seq_of_length (R := fun (_ : Fin 0 → V) => raw i g.val)
      (S := fun (_ : Fin 0 → V) z y => rawLT y z) (Definable.exists_head (vectorAffineSamples i))
      (fun _ => code_graph i g.val) (fun _ z y => def_word_lt y z) c (fun _ => hc)
  intro m x
  let T (p : Fin m → V) (y : List V) := raw i f.val (evalWord x p) y ∧ Q (evalWord x p) y
  have hd := bounded_exists (Definable.exists_head (vectorAffineSamples i)) (x.length+b) T
    (fun s y => by
      have d := (code_graph i f.val (x.map (·.subst s)) y).inter
        (ds (fun j => Fin.elim0 j) (x.map (·.subst s)) y)
      simpa only [T,eval_subst_word,Set.inter_def,Set.mem_setOf_eq] using d)
  convert hd using 1
  ext p
  change point i f g (evalWord x p) ↔ ∃ y, y.length ≤ x.length+b ∧
    raw i f.val (evalWord x p) y ∧ Q (evalWord x p) y
  constructor
  · rintro ⟨u,hu,hlt⟩
    let y := (f.val.val u).map Subtype.val
    have hr : raw i f.val (evalWord x p) y := ⟨u,_,hu,rfl,rfl⟩
    refine ⟨y,by simpa [evalWord] using hb _ _ hr,hr,_,
      ⟨u,_,hu,rfl,rfl⟩,(word_map_val_lt _ _).mpr hlt⟩
  · rintro ⟨y,_,⟨u,v,hu,rfl,rfl⟩,z,⟨u',v',hu',rfl,rfl⟩,hlt⟩
    have he : u' = u := word_unique (hu'.trans hu.symm)
    subst u'
    exact ⟨u,hu,(word_map_val_lt _ _).mp hlt⟩

/-- Empty word first, followed by the semilinear first signs on fixed lengths. -/
noncomputable abbrev order : LinearOrder F := LexSign.linearOrder (point i)
  (Definable.exists_head (vectorAffineSamples i)) (point_test i) (point_laws i) (by
    intro f g ne
    have ex : ∃ u : W, f.val.val u ≠ g.val.val u := by
      by_contra! he
      exact ne (Subtype.ext (Subtype.ext (DFunLike.ext _ _ he)))
    obtain ⟨u,hu⟩ := ex
    exact ⟨u.map Subtype.val,(lt_or_gt_of_ne hu).imp
      ((point_map i _ _ _).mpr) ((point_map i _ _ _).mpr)⟩)

/-- Strict endpoint comparison implies strict frame comparison. -/
theorem lt_of_endpoint_lt {f g : F} (h : f.val.val ⊤ < g.val.val ⊤) : (order i).lt f g := by
  apply earlier_of_empty
  · exact (point_map i f g []).mpr h
  · exact fun hh => h.asymm ((point_map i g f []).mp hh)

end KnightModel.Transfinite.FrameOrder
