import KnightModel.Transfinite.LexSignOrder

/-! # Transport of the word comparator under scalar order isomorphisms -/

namespace KnightModel.Transfinite.LexSign

variable {V U : Type*} [LinearOrder V] [LinearOrder U]

theorem first_transport (e : V ≃o U) {P Q : V → Prop} {P' Q' : U → Prop}
    (p : ∀ x, P x ↔ P' (e x)) (q : ∀ x, Q x ↔ Q' (e x)) : First P Q ↔ First P' Q' := by
  constructor
  · rintro ⟨x,hx,ex⟩
    refine ⟨e x,(p x).mp hx,?_⟩
    intro y hy h
    obtain ⟨z,rfl⟩ := e.surjective y
    exact ex z (e.le_iff_le.mp hy) ((q z).mpr h)
  · rintro ⟨y,hy,ey⟩
    obtain ⟨x,rfl⟩ := e.surjective y
    exact ⟨x,(p x).mpr hy,fun z hz h => ey (e z) (e.monotone hz) ((q z).mp h)⟩

theorem ahead_transport (e : V ≃o U) {P Q : List V → Prop} {P' Q' : List U → Prop}
    (p : ∀ w, P w ↔ P' (w.map e)) (q : ∀ w, Q w ↔ Q' (w.map e)) (n : Nat) (w : List V) :
    Ahead n P Q w ↔ Ahead n P' Q' (w.map e) := by
  induction n generalizing P Q P' Q' w with
  | zero => exact p w
  | succ n ih => exact first_transport e (fun t => ih p q (t :: w)) (fun t => ih q p (t :: w))

variable {F G : Type*}

theorem earlier_transport {R : F → F → List V → Prop} {S : G → G → List U → Prop}
    (e : V ≃o U) (f : F → G) (h : ∀ a b w, R a b w ↔ S (f a) (f b) (w.map e)) (x y : F) :
    Earlier R x y ↔ Earlier S (f x) (f y) :=
  first_transport (OrderIso.refl Nat) (fun n => ahead_transport e (h x y) (h y x) n [])
    (fun n => ahead_transport e (h y x) (h x y) n [])

end KnightModel.Transfinite.LexSign
