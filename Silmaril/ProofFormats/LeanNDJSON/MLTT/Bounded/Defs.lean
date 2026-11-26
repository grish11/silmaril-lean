module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Defs
public import Silmaril.Logic.Consequence.Institution.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u

variable {Name : Type} {S : Signature Name} {n m : Nat}

/-- Derive an event with the full-rule budget of the existing finite MLTT
logic, using translated event hypotheses. -/
def fixedDerives (H : Set (BoundedSentence n S)) (s : BoundedSentence n S) : Prop :=
  (Finite.logic.{0} n).Derives (Discrete.mk ())
    (BoundedSentence.toFinite '' H) (BoundedSentence.toFinite s)

/-- The existing fixed-budget institution equipped with bounded derivations
at every signature. -/
def fixedLogic (Name : Type) (levels : Nat) :
    LogicalSystem.{0,0,0,u + 1,u + 1} (Signature Name) where
  I := (fixedBudget.{u} Name levels).I
  Derives _ := fixedDerives
  refl _ s := by
    change fixedDerives {s} s
    rw [fixedDerives, Set.image_singleton]
    exact (Finite.logic levels).refl _ _
  mono _ {H K s} h hd := (Finite.logic levels).mono _ (Set.image_mono h) hd
  trans _ {_ K _} hK hd := by
    refine (Finite.logic levels).trans _ (Δ := BoundedSentence.toFinite '' K)
      (fun q ⟨r, h, eq⟩ => eq ▸ hK r h) ?_
    simpa only [fixedDerives, Set.image_union] using hd
  map_derives {S T} f {H s} h := by
    change fixedDerives (BoundedSentence.weaken f '' H) (BoundedSentence.weaken f s)
    unfold fixedDerives at h ⊢
    rwa [Set.image_image]

/-- The fixed-budget comparison preserves actual derivations. -/
def toFiniteMLTTLogic (Name : Type) (levels : Nat) :
    LogicalSystem.CoHom (fixedLogic.{u} Name levels) (Finite.logic.{u} levels) where
  Φ := (toFiniteMLTT Name levels).Φ
  ρ := (toFiniteMLTT Name levels).ρ
  map_derives _ _ _ h := h

/-- A sentence that fits budget `n` also fits a larger budget. -/
def BoundedSentence.include (h : n ≤ m) (s : BoundedSentence n S) : BoundedSentence m S :=
  ⟨s.val, s.property.mono h⟩

/-- Increase the rule budget, restricting tower models via the existing
finite-tower reduct and transporting proofs via `Finite.inclusionLogic`. -/
def fixedInclusionLogic (Name : Type) (h : n ≤ m) :
    LogicalSystem.CoHom (fixedLogic.{u} Name n) (fixedLogic.{u} Name m) where
  Φ := 𝟭 _
  ρ := {
    app _ := ⟨BoundedSentence.include h, Finite.modelReduct h, fun _ _ => Iff.rfl⟩
    naturality _ _ _ := Room.hom_ext rfl (by
      change Finite.modelReduct h ⋙ 𝟭 _ = 𝟭 _ ⋙ Finite.modelReduct h
      exact (Functor.comp_id _).trans (Functor.id_comp _).symm) }
  map_derives S H s hd := by
    change fixedDerives (BoundedSentence.include h '' H) (BoundedSentence.include h s)
    have transported := (Finite.inclusionLogic.{0} h).map_derives (Discrete.mk ())
      (BoundedSentence.toFinite '' H) (BoundedSentence.toFinite s) hd
    rw [Set.image_image] at transported
    rw [fixedDerives, Set.image_image]
    exact transported

/-- List-premise derivability for an unbounded consequence record at a
selected signature. -/
def consequence (S : Signature Name) :
    Silmaril.Consequence.System (List (Sentence S)) (Sentence S) :=
  Silmaril.Consequence.ER.listSys (entailment S)

/-- List-premise derivability for a consequence record at a selected
signature and rule budget. -/
def fixedConsequence (S : Signature Name) (levels : Nat) :
    Silmaril.Consequence.System (List (BoundedSentence levels S)) (BoundedSentence levels S) :=
  Silmaril.Consequence.LogicalSystem.listSys (fixedLogic.{0} Name levels) S

end Silmaril.ProofFormats.LeanNDJSON.MLTT
