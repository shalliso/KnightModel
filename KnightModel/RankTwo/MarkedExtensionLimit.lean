import KnightModel.RankTwo.ScottSubcopy
import Mathlib.Order.DirectedInverseSystem
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Direct limits of infinitary elementary chains

Every finite tuple in the union has a single stage of origin. Infinitary
conjunctions are preserved componentwise. For the existential case one
moves the witness and the old parameters into a common stage.
-/

namespace KnightModel.RankTwo.Scott.MarkedExtension

open Cardinal

variable {R : Nat → Type} {I : Type}

structure World (R : Nat → Type) where
  carrier : Type
  model : Model R carrier

def Elementary.ident {X : Type} (D : Model R X) : Elementary D D where
  toEmbedding := Function.Embedding.refl _
  truth := fun _ _ => Iff.rfl

theorem Elementary.sentence {X Y : Type} {D : Model R X} {E : Model R Y}
    (f : Elementary D E) (φ : Formula R 0) :
    BackAndForth.Satisfies D φ ↔ BackAndForth.Satisfies E φ := by
  have h : f ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → Y) := Subsingleton.elim _ _
  simpa only [BackAndForth.Satisfies,h] using f.truth φ Fin.elim0

structure Tower (R : Nat → Type) (I : Type) [Preorder I] where
  world : I → World R
  map : ∀ {i j : I}, i ≤ j → Elementary (world i).model (world j).model
  id_map : ∀ i (x : (world i).carrier), map (le_refl i) x = x
  comp_map : ∀ {i j k : I} (p : i ≤ j) (q : j ≤ k) x, map q (map p x) = map (p.trans q) x

namespace Tower

variable [LinearOrder I] (T : Tower R I)

def arrow (i j : I) (h : i ≤ j) : (T.world i).carrier ↪ (T.world j).carrier := (T.map h).toEmbedding

instance : DirectedSystem (fun i => (T.world i).carrier) (fun {_ _} h => (T.arrow _ _ h : _ → _)) where
  map_self := fun {_} x => T.id_map _ x
  map_map := fun {_ _ _} p q x => T.comp_map p q x

abbrev Carrier := DirectLimit (fun i => (T.world i).carrier) T.arrow

def insert (i : I) (x : (T.world i).carrier) : T.Carrier := ⟦⟨i,x⟩⟧

@[simp] theorem insert_map {i j : I} (h : i ≤ j) (x : (T.world i).carrier) :
    T.insert j (T.map h x) = T.insert i x := by
  change (⟦⟨j, T.arrow i j h x⟩⟧ : T.Carrier) = ⟦⟨i,x⟩⟧
  exact DirectLimit.mk_apply (F := fun l => (T.world l).carrier) (f := T.arrow) i j x h

theorem insert_injective (i : I) : Function.Injective (T.insert i) := by
  intro x y he
  obtain ⟨j,hij,_,eq⟩ := Quotient.exact he
  exact (T.map hij).injective eq

theorem exhausts (x : T.Carrier) : ∃ i y, x = T.insert i y := DirectLimit.exists_eq_mk T.arrow x

theorem tuple_stage [Nonempty I] {n} (s : Tuple T.Carrier n) :
    ∃ i, ∃ u : Tuple (T.world i).carrier n, s = T.insert i ∘ u := by
  induction n with
  | zero => exact ⟨Classical.choice ‹Nonempty I›,Fin.elim0,Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨i,x,hx⟩ := T.exhausts (s 0)
    obtain ⟨j,u,hu⟩ := ih (fun k => s k.succ)
    let k := max i j
    let v := push (T.map (le_max_left i j) x) (T.map (le_max_right i j) ∘ u)
    refine ⟨k,v,funext (Fin.cases ?_ (fun l => ?_))⟩
    · exact hx.trans (T.insert_map (le_max_left i j) x).symm
    · exact (congrFun hu l).trans (T.insert_map (le_max_right i j) (u l)).symm

def limit : World R where
  carrier := T.Carrier
  model := fun r t => ∃ i, ∃ s : Tuple (T.world i).carrier _, t = T.insert i ∘ s ∧ (T.world i).model r s

private theorem relation {n} (i : I) (r : R n) (s : Tuple (T.world i).carrier n) :
    (T.world i).model r s ↔ T.limit.model r (T.insert i ∘ s) := by
  refine ⟨fun h => ⟨i,s,rfl,h⟩, ?_⟩
  rintro ⟨j,t,eq,hr⟩
  let k := max i j
  have ss : T.map (le_max_left i j) ∘ s = T.map (le_max_right i j) ∘ t := by
    funext a
    apply T.insert_injective k
    exact (T.insert_map _ _).trans ((congrFun eq a).trans (T.insert_map _ _).symm)
  have at_j := ((T.map (le_max_right i j)).truth (.atom (.rel r id)) t).mp hr
  apply ((T.map (le_max_left i j)).truth (.atom (.rel r id)) s).mpr
  change (T.world k).model r (T.map (le_max_left i j) ∘ s)
  change (T.world k).model r (T.map (le_max_right i j) ∘ t) at at_j
  rwa [ss]

theorem holds_insert {n} (φ : Formula R n) (i : I) (s : Tuple (T.world i).carrier n) :
    φ.Holds (T.world i).model s ↔ φ.Holds T.limit.model (T.insert i ∘ s) := by
  induction φ generalizing i with
  | top => rfl
  | atom a =>
    cases a with
    | eq a b => exact (T.insert_injective i).eq_iff.symm
    | rel r vars => exact T.relation i r (s ∘ vars)
  | neg φ ih => exact not_congr (ih i s)
  | conj φ ih => exact forall_congr' (fun k => ih k i s)
  | ex φ ih =>
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨T.insert i x,?_⟩
      have he : T.insert i ∘ push x s = push (T.insert i x) (T.insert i ∘ s) :=
        funext (Fin.cases rfl (fun _ => rfl))
      exact he ▸ (ih i (push x s)).mp hx
    · rintro ⟨w,hw⟩
      obtain ⟨j,x,rfl⟩ := T.exhausts w
      let k := max i j
      have he : T.insert k ∘ push (T.map (le_max_right i j) x) (T.map (le_max_left i j) ∘ s) =
          push (T.insert j x) (T.insert i ∘ s) := by
        funext l
        exact Fin.cases (T.insert_map _ _) (fun m => T.insert_map _ _) l
      have hk := (ih k _).mpr (he ▸ hw)
      exact ((T.map (le_max_left i j)).truth (.ex φ) s).mpr ⟨_,hk⟩

def into (i : I) : Elementary (T.world i).model T.limit.model where
  toEmbedding := ⟨T.insert i,T.insert_injective i⟩
  truth := fun f t => T.holds_insert f i t

theorem into_map {i j : I} (h : i ≤ j) (x : (T.world i).carrier) :
    T.into j (T.map h x) = T.into i x := T.insert_map h x

/-- A compatible family of embeddings into a fixed outer model descends
to an elementary embedding of the direct limit. -/
def descend [Nonempty I] {Z : World R} (e : ∀ i, Elementary (T.world i).model Z.model)
    (comm : ∀ i j (h : i ≤ j) x, e i x = e j (T.map h x)) : Elementary T.limit.model Z.model where
  toEmbedding := ⟨DirectLimit.lift T.arrow (fun i x => e i x) comm,
    DirectLimit.lift_injective T.arrow _ comm (fun i => (e i).injective)⟩
  truth := by
    intro n φ s
    obtain ⟨i,t,rfl⟩ := T.tuple_stage s
    exact (T.holds_insert φ i t).symm.trans ((e i).truth φ t)

@[simp] theorem descend_into [Nonempty I] {Z : World R} (e : ∀ i, Elementary (T.world i).model Z.model)
    (comm : ∀ i j (h : i ≤ j) x, e i x = e j (T.map h x)) (i : I) (x : (T.world i).carrier) :
    T.descend e comm (T.into i x) = e i x := rfl

theorem mk_limit_le (κ : Cardinal) (inf : ℵ₀ ≤ κ) (hi : #I ≤ κ)
    (small : ∀ i, #(T.world i).carrier ≤ κ) : #T.limit.carrier ≤ κ := calc
  _ ≤ #(Σ i, (T.world i).carrier) := mk_le_of_surjective
    (f := fun z : Σ i, (T.world i).carrier => T.insert z.1 z.2)
    (fun x => by obtain ⟨i,y,rfl⟩ := T.exhausts x; exact ⟨⟨i,y⟩,rfl⟩)
  _ = Cardinal.sum (fun i => #(T.world i).carrier) := mk_sigma _
  _ ≤ Cardinal.sum (fun _ : I => κ) := sum_le_sum _ _ small
  _ = #I * κ := sum_const' _ _
  _ ≤ κ * κ := mul_le_mul' hi le_rfl
  _ = κ := mul_eq_self inf

end Tower
end KnightModel.RankTwo.Scott.MarkedExtension
