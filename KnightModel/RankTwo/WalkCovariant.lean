import KnightModel.RankTwo.AtlasWalk

/-! # Covariance of the actual transports at interior limit sectors -/

namespace KnightModel.RankTwo

namespace TailShape

/-- Enlarging the enclosing chart by a copied prefix preserves its last fold. -/
def prepend {A : Type*} (p : List A) (h : TailShape A) : TailShape A :=
  ⟨p ++ h.prefix, h.extra⟩

theorem apply_prepend {A : Type*} [LinearOrder A] (shift : ∀ a : A, Set.Ici a ≃o A)
    (p : List A) (h : TailShape A) (w : Word A) :
    (h.prepend p).apply shift w = Word.prepend p (h.apply shift w) :=
  List.append_assoc _ _ _

end TailShape

namespace CoherentLadders

variable {J A : Type*} [LinearOrder J] [WellFoundedLT J] [LinearOrder A]
variable (C : CoherentLadders J A)

/-- Compare charts on an interval ending at the interior limit, including its
marked endpoint. Its last-fold case is unchanged. -/
theorem fits_prepend {a b c n : J} {p : List A} {h : TailShape A} (hn : n < a)
    (copy : ∀ x, n < x → x ≤ a → C.word b x = p ++ C.word c x)
    (hh : C.Fits c a h) : C.Fits b a (h.prepend p) := by
  obtain ⟨⟨m, hm, htail⟩, hend, hslot⟩ := hh
  refine ⟨⟨max n m, max_lt hn hm, ?_⟩, ?_, hslot⟩
  · intro x hmx hxa
    change C.word b x = (p ++ h.prefix) ++ C.word a x
    rw [copy x ((le_max_left _ _).trans_lt hmx) hxa.le,
      htail x ((le_max_right _ _).trans_lt hmx) hxa, List.append_assoc]
  · change C.word b a = (p ++ h.prefix) ++ h.extra.toList
    rw [copy a hn le_rfl, hend, List.append_assoc]

theorem shape_prepend {a b c n : J} {p : List A}
    (hab : a ≤ b) (hac : a ≤ c) (hn : n < a)
    (lim : ∀ m < a, ∃ x, m < x ∧ x < a)
    (copy : ∀ x, n < x → x ≤ a → C.word b x = p ++ C.word c x) :
    C.shape hab ⟨n, hn⟩ = (C.shape hac ⟨n, hn⟩).prepend p :=
  C.fits_unique lim (C.shape_fits _ _) (C.fits_prepend hn copy (C.shape_fits _ _))

variable (shift : ∀ a : A, Set.Ici a ≃o A) (o d : A) (hd : o < d)
    (upper : ∀ a : A, Set.Ioi a ≃o Set.Ioi o)

theorem transports_limit_apply {b a : J} (hab : a ≤ b) (pos : ∃ i, i < a)
    (lim : ∀ m < a, ∃ x, m < x ∧ x < a) (w : C.markedRows.sector a a) :
    (C.transports shift o d hd upper hab w : Word A) = (C.shape hab pos).apply shift w := by
  classical
  have hp : ¬∃ p < a, ∀ i < a, i ≤ p := by
    rintro ⟨p, hpa, hp⟩
    obtain ⟨i, hpi, hia⟩ := lim p hpa
    exact (not_le_of_gt hpi) (hp i hia)
  unfold transports
  rw [dif_pos pos, dif_neg hp]
  rfl

/-- The chosen sector transports on a copied interior limit commute with the
outer prefix substitution, at every word of the native sector. -/
theorem transports_limit_prepend {a b c n : J} {p : List A}
    (hab : a ≤ b) (hac : a ≤ c) (hn : n < a) (lim : ∀ m < a, ∃ x, m < x ∧ x < a)
    (copy : ∀ x, n < x → x ≤ a → C.word b x = p ++ C.word c x)
    (w : C.markedRows.sector a a) :
    (C.transports shift o d hd upper hab w : Word A) =
      Word.prepend p (C.transports shift o d hd upper hac w : Word A) := by
  rw [C.transports_limit_apply shift o d hd upper hab ⟨n, hn⟩ lim,
      C.transports_limit_apply shift o d hd upper hac ⟨n, hn⟩ lim,
      C.shape_prepend hab hac hn lim copy, TailShape.apply_prepend]

end CoherentLadders
end KnightModel.RankTwo
