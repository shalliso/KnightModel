import KnightModel.RankTwo.ScottRestrictionDependence

/-! # Countably many unary orbital functions on each comparison fiber -/

namespace KnightModel.RankTwo.Scott.SentenceLabels

open Set Restriction

variable {R : ℕ → Type u} {M N : Type} {C : Presentation R M} {D : Model R M} {E : Model R N}
    {h : BackAndForth.Satisfies E (C.sentence D)}

local notation "F" => C.system D E h
local notation "L" => scottLabels C D E h

noncomputable section

/-- The pointed label identifies a partial orbital map. Rank zero of its value
says this label can take at most one value at a specified input. -/
def Orbital {n} (t : Tuple N n) (k : Nat) (x y : N) : Prop :=
  y ∈ lowFiber F 0 (push x t) ∧ (L).label (push y (push x t)) = k

theorem Orbital.unique {n} {t : Tuple N n} {k : Nat} {x y z : N}
    (hy : Orbital (h := h) t k x y) (hz : Orbital (h := h) t k x z) : y = z :=
  unique_by_zero hy.1 (hy.2.trans hz.2.symm)

theorem Orbital.move {n} {t : Tuple N n} {k : Nat} {x y u v : N}
    (hy : Orbital (h := h) t k x y) {f : (L).Motion} (ht : ∀ i, f.Mem (t i) (t i))
    (hx : f.Mem x u) (hv : f.Mem y v) : Orbital (h := h) t k u v := by
  have eqn := f.same_of_mems (s := push y (push x t)) (t := push v (push u t)) (Fin.cases hv (Fin.cases hx ht))
  exact ⟨(lowFiber_congr C D E h eqn).mp hy.1,eqn.symm.trans hy.2⟩

/-- Extend the orbital map by the identity wherever this pointed label is absent. -/
def orbitalMap {n} (t : Tuple N n) (O : Set N) (k : Nat) (x : O) : O := by
  classical
  exact if p : ∃ y : O, Orbital (h := h) t k x.val y.val then p.choose else x

theorem orbitalMap_apply {n} {t : Tuple N n} {O : Set N} {k : Nat} {x y : O}
    (hy : Orbital (h := h) t k x.val y.val) : orbitalMap (h := h) t O k x = y := by
  classical
  let p : ∃ y : O, Orbital (h := h) t k x.val y.val := ⟨y,hy⟩
  unfold orbitalMap
  rw [dif_pos p]
  exact Subtype.ext (p.choose_spec.unique hy)

theorem orbitalMap_compare {n} {t : Tuple N n} {O : Set N} {x y : O}
    (cmp : x.val ∈ lowFiber F 0 (push y.val t) ∨ y.val ∈ lowFiber F 0 (push x.val t)) :
    (∃ k, x = orbitalMap (h := h) t O k y) ∨ (∃ k, y = orbitalMap (h := h) t O k x) := by
  rcases cmp with hx | hy
  · exact Or.inl ⟨_,(orbitalMap_apply (x := y) (y := x) ⟨hx,rfl⟩).symm⟩
  · exact Or.inr ⟨_,(orbitalMap_apply (x := x) (y := y) ⟨hy,rfl⟩).symm⟩

/-- Transport the domain and the value at once, extending the partial motion
only by one point. This works on an arbitrary target model of the sentence. -/
theorem orbital_witness_move {n} {t : Tuple N n} {O : Set N}
    (stable : ∀ (g : (L).Motion), (∀ i, g.Mem (t i) (t i)) → ∀ x ∈ O, ∀ y, g.Mem x y → y ∈ O)
    {k : Nat} {x y : O} (f : (L).Motion) (fix : ∀ i, f.Mem (t i) (t i)) (xy : f.Mem x.val y.val)
    {u : O} (hu : Orbital (h := h) t k x.val u.val) :
    ∃ (g : (L).Motion) (v : O),
      (∀ a b, f.Mem a b → g.Mem a b) ∧ g.Mem u.val v.val ∧ Orbital (h := h) t k y.val v.val := by
  obtain ⟨g,v,hv,inc⟩ := f.extend_point u.val
  have fix' i := inc _ _ (fix i)
  exact ⟨g,⟨v,stable g fix' u.val u.property v hv⟩,inc,hv,hu.move fix' (inc _ _ xy) hv⟩

theorem orbitalMap_move {n} {t : Tuple N n} {O : Set N}
    (stable : ∀ (g : (L).Motion), (∀ i, g.Mem (t i) (t i)) → ∀ x ∈ O, ∀ y, g.Mem x y → y ∈ O)
    (k : Nat) {x y : O} (f : (L).Motion) (fix : ∀ i, f.Mem (t i) (t i)) (xy : f.Mem x.val y.val) :
    ∃ g : (L).Motion, (∀ a b, f.Mem a b → g.Mem a b) ∧
      g.Mem (orbitalMap (h := h) t O k x).val (orbitalMap (h := h) t O k y).val := by
  classical
  by_cases present : ∃ u : O, Orbital (h := h) t k x.val u.val
  · obtain ⟨u,hu⟩ := present
    obtain ⟨g,v,inc,uv,hv⟩ := orbital_witness_move stable f fix xy hu
    exact ⟨g,inc,orbitalMap_apply hu ▸ orbitalMap_apply hv ▸ uv⟩
  · have absent : ¬ ∃ v : O, Orbital (h := h) t k y.val v.val := by
      rintro ⟨v,hv⟩
      obtain ⟨_,u,_,_,hu⟩ := orbital_witness_move stable f.flip
        (fun i => Labels.Motion.mem_flip.mpr (fix i)) (Labels.Motion.mem_flip.mpr xy) hv
      exact present ⟨u,hu⟩
    refine ⟨f,fun _ _ r => r,?_⟩
    simpa only [orbitalMap,dif_neg present,dif_neg absent] using xy

end
end KnightModel.RankTwo.Scott.SentenceLabels
