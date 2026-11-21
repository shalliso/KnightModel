import KnightModel.RankTwo.MarkedExtensionTower
import KnightModel.RankTwo.MarkedExtensionLimit

/-! # Elementary towers from strict transition maps

A diagram can carry marks or cardinal bounds in its objects. The world
projection keeps the original carriers and sends every strict arrow to the
specified elementary embedding.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Transfinite

universe u v

variable {O : Type u} {H : O → O → Type v} {compose : ∀ {a b c}, H a b → H b c → H a c}
variable {J : Type} [LinearOrder J] {R : ℕ → Type}
variable (D : Diagram H compose J) (realize : O → World R)
variable (emb : ∀ {a b}, H a b → Elementary (realize a).model (realize b).model)
variable (respect : ∀ {a b c} (f : H a b) (g : H b c) (x : (realize a).carrier),
  emb (compose f g) x = emb g (emb f x))

private def extendMap {i j : J} (p : i ≤ j) :
    Elementary (realize (D.obj i)).model (realize (D.obj j)).model :=
  if eq : i = j then eq ▸ Elementary.ident (realize (D.obj i)).model
  else emb (D.map (lt_of_le_of_ne p eq))

private theorem extendMap_self (i : J) (x : (realize (D.obj i)).carrier) :
    extendMap D realize emb (le_refl i) x = x := by
  simp only [extendMap, dif_pos rfl]
  rfl

private theorem extendMap_strict {i j : J} (h : i < j) :
    extendMap D realize emb h.le = emb (D.map h) := by
  simp only [extendMap, dif_neg h.ne]

/-- Add the identity maps to a strict transfinite diagram of elementary arrows. -/
def ofStrict : Tower R J where
  world i := realize (D.obj i)
  map := extendMap D realize emb
  id_map := extendMap_self D realize emb
  comp_map := by
    intro i j k p q x
    rcases p.eq_or_lt with rfl | ij
    · rw [extendMap_self]
    rcases q.eq_or_lt with rfl | jk
    · rw [extendMap_self]
    · rw [extendMap_strict D realize emb ij, extendMap_strict D realize emb jk,
        extendMap_strict D realize emb (lt_trans ij jk), ← D.trans ij jk, respect]

/-- On a genuine increasing pair, the non-strict tower uses its original map. -/
theorem ofStrict_map_lt {i j : J} (h : i < j) :
    (ofStrict D realize emb respect).map h.le = emb (D.map h) :=
  extendMap_strict D realize emb h

/-- Both images agree inside the direct limit. -/
theorem ofStrict_into_map_lt {i j : J} (h : i < j) (x : (realize (D.obj i)).carrier) :
    (ofStrict D realize emb respect).into j (emb (D.map h) x) =
    (ofStrict D realize emb respect).into i x := by
  rw [← ofStrict_map_lt D realize emb respect h]
  exact (ofStrict D realize emb respect).insert_map h.le x

/-- One fresh point at every index gives that many distinct points in the limit.
It is enough to check freshness against each incoming strict map separately. -/
theorem ofStrict_fresh_injective (point : ∀ j, (realize (D.obj j)).carrier)
    (fresh : ∀ i j (h : i < j) x, emb (D.map h) x ≠ point j) :
    Function.Injective (fun j => (ofStrict D realize emb respect).into j (point j)) := by
  have separate {i j : J} (h : i < j) :
      (ofStrict D realize emb respect).into i (point i) ≠
      (ofStrict D realize emb respect).into j (point j) := by
    intro eq
    apply fresh i j h (point i)
    exact ((ofStrict D realize emb respect).into j).toEmbedding.injective
      ((ofStrict_into_map_lt D realize emb respect h (point i)).trans eq)
  intro i j eq
  rcases lt_trichotomy i j with h | h | h
  · exact (separate h eq).elim
  · exact h
  · exact (separate h eq.symm).elim

end KnightModel.RankTwo.Scott.MarkedExtension
