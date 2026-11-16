module

public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Closed-theory semantics for entailment relations

A model is a deductively closed set of sentences, satisfaction is membership,
and a translation reduces models by inverse image. This syntactic semantics is
sound and complete by construction. It makes no claim about consistency or
about a separate concrete class of mathematical models.
-/

namespace Silmaril.Logic.Institution.Syntactic

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory

universe w

noncomputable section

/-- A deductively closed set of judgments for an actual entailment relation. -/
structure Theory (S : ER.{w}) where
  sentences : Set S.Sen
  closed : ∀ φ, S.Derives sentences φ → φ ∈ sentences

@[ext] theorem Theory.ext {S : ER.{w}} {T U : Theory S}
    (h : T.sentences = U.sentences) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- The least deductively closed theory containing the supplied sentences. -/
def generated (S : ER.{w}) (Γ : Set S.Sen) : Theory S where
  sentences := {φ | S.Derives Γ φ}
  closed _ h := S.trans (fun _ hφ => hφ) (S.mono Set.subset_union_right h)

/-- Inverse image of a closed theory is closed because the translation preserves derivability. -/
def reduct {S T : ER.{w}} (f : S ⟶ T) (M : Theory T) : Theory S where
  sentences := f.sen ⁻¹' M.sentences
  closed φ h := M.closed _ (T.mono (by rintro _ ⟨ψ, hψ, rfl⟩; exact hψ) (f.map_derives h))

/-- A syntactic room with discrete closed-theory models. -/
def room (S : ER.{w}) : Room.{w,w,w} :=
  ⟨S.Sen, Cat.of (Discrete (Theory S)), fun M φ => φ ∈ M.as.sentences⟩

/-- Derivability-preserving translations induce satisfaction-preserving corridors. -/
def corridor {S T : ER.{w}} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨f.sen, Discrete.functor (fun M => Discrete.mk (reduct f M)), fun _ _ => Iff.rfl⟩

/-- The construction is functorial, including the contravariant model reduction. -/
def toRooms : ER.{w} ⥤ Room.{w,w,w} where
  obj := room
  map := corridor
  map_id S := by
    apply Corridor.ext
    · rfl
    · change Discrete.functor (fun M : Theory S => Discrete.mk (reduct (𝟙 S) M)) = 𝟭 _
      exact Functor.ext (fun M => by cases M; rfl) (fun _ _ _ => Subsingleton.elim _ _)
  map_comp f g := by
    apply Corridor.ext
    · rfl
    · rfl

/-- A room, viewed as a one-signature institution. -/
def oneSignature (R : Room.{w,w,w}) : Inst.{0,0,w,w,w} where
  Sign := Discrete Unit
  I := (Functor.const (Discrete Unit)).obj R

/-- A corridor induces an actual institution comorphism. -/
def oneSignatureMap {R S : Room.{w,w,w}} (f : R ⟶ S) :
    Inst.CoHom (oneSignature R) (oneSignature S) where
  Φ := 𝟭 (Discrete Unit)
  ρ :=
    { app := fun _ => f
      naturality := by intro a b σ; change 𝟙 R ≫ f = f ≫ 𝟙 S; simp }

/-- Map rooms and corridors functorially into the category of institutions. -/
def roomsToInstitutions : Room.{w,w,w} ⥤ CoIns.{0,0,w,w,w} where
  obj := oneSignature
  map := oneSignatureMap
  map_id R := by
    apply Inst.CoHom.ext rfl
    simp only [eqToHom_refl, Category.comp_id]
  map_comp f g := by
    apply Inst.CoHom.ext rfl
    simp only [eqToHom_refl, Category.comp_id]

/-- The institution functor for closed-theory semantics. -/
def toInstitutions : ER.{w} ⥤ CoIns.{0,0,w,w,w} := toRooms ⋙ roomsToInstitutions

end
end Silmaril.Logic.Institution.Syntactic
