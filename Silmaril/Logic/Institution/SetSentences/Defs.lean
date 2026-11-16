module

public import Silmaril.Logic.Institution.Morphism

@[expose] public section
namespace Silmaril.Logic.Institution.SetSentences
open CategoryTheory Silmaril.Logic.Institution
universe u v w m₁ m₂

/-- Arbitrary sets of sentences, interpreted conjunctively. The model category,
including every underlying model arrow, is unchanged. `Set R.Sen : Type w`,
so the public room and institution sentence universe does not increase. -/
def room (R : Room.{w,m₁,m₂}) : Room.{w,m₁,m₂} :=
  ⟨Set R.Sen, R.Mod, fun M Γ => ∀ φ ∈ Γ, R.Sat M φ⟩

/-- Sentence sets translate by direct image, even for noninjective maps. -/
def corridor {R S : Room.{w,m₁,m₂}} (c : R ⟶ S) : room R ⟶ room S :=
  ⟨Set.image c.sen, c.mod, by
    intro M Γ
    constructor
    · intro h φ hφ
      exact (c.sat M φ).mp (h _ ⟨φ, hφ, rfl⟩)
    · intro h ψ hψ
      obtain ⟨φ, hφ, rfl⟩ := hψ
      exact (c.sat M φ).mpr (h φ hφ)⟩

theorem corridor_id (R : Room.{w,m₁,m₂}) : corridor (𝟙 R) = 𝟙 (room R) := by
  apply Room.hom_ext
  · funext Γ
    exact Set.image_id Γ
  · rfl

theorem corridor_comp {R S T : Room.{w,m₁,m₂}} (c : R ⟶ S) (d : S ⟶ T) :
    corridor (c ≫ d) = corridor c ≫ corridor d := by
  apply Room.hom_ext
  · funext Γ
    exact (Set.image_image d.sen c.sen Γ).symm
  · rfl

/-- The conjunction lift is an actual endofunctor of rooms. -/
def rooms : Room.{w,m₁,m₂} ⥤ Room.{w,m₁,m₂} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- Signatures and reduct functors remain precisely those of the input. -/
def institution {Sign : Type u} [Category.{v} Sign]
    (I : Sign ⥤ Room.{w,m₁,m₂}) : Sign ⥤ Room.{w,m₁,m₂} := I ⋙ rooms

/-- A single sentence is represented by its singleton conjunction. -/
def singletonCorridor (R : Room.{w,m₁,m₂}) : R ⟶ room R :=
  ⟨(fun φ : R.Sen => ({φ} : Set R.Sen)), 𝟭 R.Mod, by
    intro M φ
    change (∀ ψ ∈ ({φ} : Set R.Sen), R.Sat M ψ) ↔ R.Sat M φ
    simp only [Set.mem_singleton_iff, forall_eq]⟩

set_option backward.isDefEq.respectTransparency false in
def singletonNatural {Sign : Type u} [Category.{v} Sign]
    (I : Sign ⥤ Room.{w,m₁,m₂}) : I ⟶ institution I where
  app S := singletonCorridor (I.obj S)
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext φ
      change ({(I.map f).sen φ} : Set (I.obj T).Sen) = (I.map f).sen '' {φ}
      simp only [Set.image_singleton]
    · change (I.map f).mod ⋙ 𝟭 _ = 𝟭 _ ⋙ (I.map f).mod
      rw [Functor.comp_id, Functor.id_comp]

def inst (A : Inst.{u,v,w,m₁,m₂}) : Inst.{u,v,w,m₁,m₂} :=
  ⟨A.Sign, institution A.I⟩

def singleton (A : Inst.{u,v,w,m₁,m₂}) : Inst.CoHom A (inst A) :=
  ⟨𝟭 A.Sign, singletonNatural A.I⟩

end Silmaril.Logic.Institution.SetSentences
