import KnightModel.Transfinite.SumLanguage

/-! # Long increasing sequences in the lexicographic sum -/

namespace KnightModel.Transfinite.NamedSum
open Cardinal Ordinal

private theorem accessible {A : ℕ → Type} [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    (i : ℕ) (x : A i) : Acc ((· < ·) : Carrier A → Carrier A → Prop) (inject i x) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    induction x using WellFoundedLT.induction with
    | ind x ix =>
      constructor
      rintro ⟨j,y⟩ lt
      rcases Sigma.Lex.lt_def.mp lt with small | ⟨eq,less⟩
      · exact ih j small y
      · change j = i at eq
        subst j
        exact ix y less

private def componentsEmbedding {A B : ℕ → Type} [∀ i, LinearOrder (A i)] [∀ i, LinearOrder (B i)]
    (f : ∀ i, A i ↪o B i) : Carrier A ↪o Carrier B :=
  OrderEmbedding.ofStrictMono (fun p => inject (tag p) (f _ (ofLex p).2)) (by
    rintro ⟨i,x⟩ ⟨j,y⟩ lt
    rcases Sigma.Lex.lt_def.mp lt with small | ⟨eq,less⟩
    · exact Sigma.Lex.left _ _ small
    · change i = j at eq
      subst j
      exact Sigma.Lex.right _ _ ((f i).strictMono less))

/-- Each input contributes an initial ordinal sequence. Their ordered sum
contains an increasing sequence of the supremum cardinal's initial ordinal. -/
noncomputable def longSequence {N : ℕ → Type} [∀ i, LinearOrder (N i)] (k : ℕ → Cardinal)
    (κ : Cardinal) (sup : ∀ c, (∀ i, k i ≤ c) → κ ≤ c)
    (seq : ∀ i, (k i).ord.ToType ↪o N i) : κ.ord.ToType ↪o Carrier N := by
  let A (i : ℕ) := (k i).ord.ToType
  let W := Carrier A
  letI : WellFoundedLT W := ⟨⟨fun ⟨i,x⟩ => accessible i x⟩⟩
  letI : IsWellOrder W ((· < ·) : W → W → Prop) := inferInstance
  have bound : κ ≤ #W := by
    apply sup
    intro i
    have h := Cardinal.mk_le_of_injective (inject_injective (X := A) i)
    simpa [A, Cardinal.mk_toType] using h
  have limit : κ.ord ≤ Ordinal.type ((· < ·) : W → W → Prop) :=
    (ord_le_ord.mpr bound).trans (ord_le_type _)
  let e (x : κ.ord.ToType) : W := Ordinal.enum ((· < ·) : W → W → Prop)
    ⟨x.toOrd.val,lt_of_lt_of_le (show x.toOrd.val < κ.ord from x.toOrd.property) limit⟩
  have strict : StrictMono e := fun _ _ h =>
    (Ordinal.enum_lt_enum (r := ((· < ·) : W → W → Prop))).mpr (Ordinal.ToType.mk.symm.strictMono h)
  exact (OrderEmbedding.ofStrictMono e strict).trans (componentsEmbedding seq)

end KnightModel.Transfinite.NamedSum
