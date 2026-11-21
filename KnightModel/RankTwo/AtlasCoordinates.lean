import KnightModel.RankTwo.AtlasFrames

/-! # Restricting coordinate maps to a smaller image

All comparisons use the actual graph of the two maps. The restricted
coordinate has graph `g y = f x`, which is composition with the inverse
relation even when the latter is partial. -/

namespace KnightModel.RankTwo.CoordinateFamily

open Set

variable {W : Type*} [LinearOrder W] [OrderTop W]

/-- A coordinate has a full principal initial segment as its image. -/
def FullInitial (f : W ↪o W) : Prop := Set.range f = Iic (f ⊤)

theorem fullInitial_id : FullInitial (OrderIso.refl W).toOrderEmbedding := by
  ext w
  exact ⟨fun _ => le_top, fun _ => ⟨w, rfl⟩⟩

theorem FullInitial.comp {f g : W ↪o W} (hf : FullInitial f) (hg : FullInitial g) :
    FullInitial (f.trans g) := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact g.monotone (f.monotone le_top)
  · intro hz
    have hg' : z ≤ g ⊤ := hz.trans (g.monotone le_top)
    obtain ⟨y,hy⟩ : z ∈ Set.range g := hg ▸ hg'
    have hy' : y ≤ f ⊤ := g.le_iff_le.mp (hy ▸ hz)
    obtain ⟨w,hw⟩ : y ∈ Set.range f := hf ▸ hy'
    exact ⟨w,(congrArg g hw).trans hy⟩

noncomputable def coordIso (f : W ↪o W) (hf : FullInitial f) : W ≃o Iic (f ⊤) :=
  let e : W → Iic (f ⊤) := fun w => ⟨f w,f.monotone le_top⟩
  StrictMono.orderIsoOfSurjective e (fun _ _ h => f.strictMono h) (by
    intro z
    obtain ⟨w,hw⟩ : z.val ∈ Set.range f := by rw [hf]; exact z.property
    exact ⟨w,Subtype.ext hw⟩)

/-- The extensional restricted map `g⁻¹ f`. -/
noncomputable def divide (f g : W ↪o W) (hg : FullInitial g) (leEnd : f ⊤ ≤ g ⊤) : W ↪o W :=
  OrderEmbedding.ofStrictMono (fun w => (coordIso g hg).symm ⟨f w,(f.monotone le_top).trans leEnd⟩)
    (fun _ _ h => (coordIso g hg).symm.strictMono (f.strictMono h))

@[simp] theorem divide_apply (f g : W ↪o W) (hg : FullInitial g) (leEnd : f ⊤ ≤ g ⊤) (x : W) :
    g (divide f g hg leEnd x) = f x :=
  congrArg Subtype.val ((coordIso g hg).apply_symm_apply ⟨f x,(f.monotone le_top).trans leEnd⟩)

theorem divide_graph (f g : W ↪o W) (hg : FullInitial g) (leEnd : f ⊤ ≤ g ⊤) (x y : W) :
    divide f g hg leEnd x = y ↔ ∃ z, f x = z ∧ g y = z := by
  refine ⟨fun h => ⟨f x,rfl,h ▸ divide_apply _ _ _ _ x⟩, ?_⟩
  rintro ⟨z,rfl,hy⟩
  exact g.injective ((divide_apply _ _ _ _ x).trans hy.symm)

theorem fullInitial_divide (f g : W ↪o W) (hf : FullInitial f) (hg : FullInitial g)
    (leEnd : f ⊤ ≤ g ⊤) : FullInitial (divide f g hg leEnd) := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact (divide f g hg leEnd).monotone le_top
  · intro hy
    have hgy : g y ≤ f ⊤ := (g.monotone hy).trans_eq (divide_apply _ _ _ _ _)
    obtain ⟨x,hx⟩ : g y ∈ Set.range f := hf ▸ hgy
    exact ⟨x,g.injective ((divide_apply _ _ _ _ _).trans hx)⟩

end KnightModel.RankTwo.CoordinateFamily
