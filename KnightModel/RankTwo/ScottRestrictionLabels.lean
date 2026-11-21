import KnightModel.RankTwo.RestrictionCardinal

/-! # Natural-number orbit labels in arbitrary models of a Scott sentence -/

namespace KnightModel.RankTwo.Scott

namespace BackAndForth

variable {R : ℕ → Type u} {M N : Type} {D : Model R M} {E : Model R N}
variable (F : BackAndForth D E) (C : Presentation R M)
include C

/-- Any two source tuples lifting the same finite target tuple are pointwise
matched by one source automorphism. -/
theorem lifts_aligned {n} {s u : Tuple M n} {t : Tuple N n} (hs : F.Lifts s t) (hu : F.Lifts u t) :
    ∃ g : ↥(automorphismGroup D), ∀ i, g • s i = u i := by
  let e := F.through.pointedIsoOfEnumerations (s := s) (t := u) ⟨t,hs,hu⟩ C.enum C.onto C.enum C.onto
  exact ⟨(automorphismEquivRelIso D).symm e.val,e.property⟩

/-- The relative rank of a pointed target tuple is the rank of every source
lift, even when the chosen back-and-forth is not saturated under source
automorphisms. -/
theorem lowFiber_iff_liftRank {n k} {x : M} {s : Tuple M k} {y : N} {t : Tuple N k}
    (hs : F.Lifts (push x s) (push y t)) : y ∈ lowFiber F n t ↔ ModelRankLE D n (List.ofFn s) x := by
  refine ⟨?_,fun h => ⟨x,s,h,hs⟩⟩
  rintro ⟨v,u,hv,hu⟩
  obtain ⟨g,hg⟩ := F.lifts_aligned C hu hs
  have hx : g • v = x := hg 0
  have he : (List.ofFn u).map (g • ·) = List.ofFn s := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => hg i.succ)
  simpa only [he,hx] using (hv.smul g)

end BackAndForth

namespace SentenceLabels

variable {R : ℕ → Type u} {M N : Type} (C : Presentation R M) (D : Model R M) (E : Model R N)
    (h : BackAndForth.Satisfies E (C.sentence D))
include h

/-- For the canonical Scott system, taking all finite restrictions gives
exactly the same matched tuples. -/
theorem lifts_iff {n} (s : Tuple M n) (t : Tuple N n) :
    (C.system D E h).Lifts s t ↔ (C.label D s).Holds E t :=
  ⟨fun m => ((C.system D E h).closure.holds_iff _ m).mp (C.self_label D s),
    fun m => (C.system D E h).lifts_of_match m⟩

theorem exists_label {n} (t : Tuple N n) : ∃ s : Tuple M n, (C.label D s).Holds E t := by
  induction n with
  | zero =>
    have he : t = Fin.elim0 := Subsingleton.elim _ _
    exact ⟨Fin.elim0,he ▸ ((C.sentence_iff D E).mp h).1⟩
  | succ n ih =>
    obtain ⟨s,hs⟩ := ih (fun i => t i.succ)
    obtain ⟨x,hx⟩ := (C.system D E h).back (s := s) (t := fun i => t i.succ) hs (t 0)
    have he : push (t 0) (fun i => t i.succ) = t := funext (Fin.cases rfl (fun _ => rfl))
    exact ⟨push x s,he ▸ hx⟩

theorem exists_number {n} (t : Tuple N n) : ∃ i, (C.label D (C.tuples n i)).Holds E t := by
  obtain ⟨s,hs⟩ := exists_label C D E h t
  obtain ⟨i,hi⟩ := C.tuples_onto s
  exact ⟨i,hi ▸ hs⟩

noncomputable def number {n} (t : Tuple N n) : Nat := by
  classical
  exact Nat.find (exists_number C D E h t)

theorem number_spec {n} (t : Tuple N n) :
    (C.label D (C.tuples n (number C D E h t))).Holds E t := by
  classical
  exact Nat.find_spec (exists_number C D E h t)

theorem theory_of_label {n} {s : Tuple M n} {t u : Tuple N n}
    (ht : (C.label D s).Holds E t) (hu : (C.label D s).Holds E u) : Presentation.TheoryEq E t u :=
  fun φ => ((C.system D E h).holds_iff φ (s := s) (t := t) ht).symm.trans ((C.system D E h).holds_iff φ (s := s) (t := u) hu)

theorem number_eq_iff {n} (t u : Tuple N n) :
    number C D E h t = number C D E h u ↔ Presentation.TheoryEq E t u := by
  classical
  refine ⟨fun he => theory_of_label C D E h ((number_spec C D E h t) : _) (he ▸ number_spec C D E h u), ?_⟩
  intro eqt
  exact le_antisymm (Nat.find_min' _ ((eqt _).mpr (number_spec C D E h u)))
    (Nat.find_min' _ ((eqt _).mp (number_spec C D E h t)))

theorem number_select {n k} {t u : Tuple N n} (he : number C D E h t = number C D E h u)
    (s : Fin k → Fin n) : number C D E h (t ∘ s) = number C D E h (u ∘ s) := by
  have ht := (lifts_iff C D E h _ _).mpr (number_spec C D E h t)
  have hu := (lifts_iff C D E h _ _).mpr ((number_eq_iff C D E h t u).mp he _ |>.mp
    (number_spec C D E h t))
  apply (number_eq_iff C D E h _ _).mpr
  exact theory_of_label C D E h ((lifts_iff C D E h _ _).mp (ht.select _ s))
    ((lifts_iff C D E h _ _).mp (hu.select _ s))

theorem number_extend {n} {t u : Tuple N n} (he : number C D E h t = number C D E h u) (x : N) :
    ∃ y, number C D E h (push x t) = number C D E h (push y u) := by
  have ht := number_spec C D E h t
  have hu := ((number_eq_iff C D E h t u).mp he _).mp ht
  obtain ⟨a,ha⟩ := (C.system D E h).back (s := C.tuples n (number C D E h t)) (t := t) ht x
  obtain ⟨b,hb⟩ := (C.system D E h).forth (s := C.tuples n (number C D E h t)) (t := u) hu a
  exact ⟨b,(number_eq_iff C D E h _ _).mpr (theory_of_label C D E h ha hb)⟩

theorem lowFiber_congr {n k} {s t : Tuple N k} {x y : N}
    (he : number C D E h (push x s) = number C D E h (push y t)) :
    x ∈ lowFiber (C.system D E h) n s ↔ y ∈ lowFiber (C.system D E h) n t := by
  have fwd {r z : Tuple N (k+1)} (q : Presentation.TheoryEq E r z) (v : Tuple M (k+1))
      (hv : (C.system D E h).Lifts v r) : (C.system D E h).Lifts v z :=
    (lifts_iff C D E h _ _).mpr ((q _).mp ((lifts_iff C D E h _ _).mp hv))
  have q := (number_eq_iff C D E h _ _).mp he
  exact ⟨fun ⟨a,v,hv,hx⟩ => ⟨a,v,hv,fwd q _ hx⟩,
    fun ⟨a,v,hv,hy⟩ => ⟨a,v,hv,fwd (fun φ => (q φ).symm) _ hy⟩⟩

end SentenceLabels
end KnightModel.RankTwo.Scott
