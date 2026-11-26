module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Packed.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Packed.Institution

/-! # Packing as a comorphism of ordered weak-tree institutions -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.PackedInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room Inst)

universe u v

variable {κ : Type (u + 1)} {P Q S : FlatInstitution.Signature.{u, v} κ} {A : Ty κ}

@[simp] theorem Sentence.map_id (s : Sentence P A) : s.map (𝟙 P) = s :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution.sentence_map_id s

theorem Sentence.map_comp (g : P ⟶ Q) (h : Q ⟶ S) (s : Sentence P A) :
    s.map (g ≫ h) = (s.map g).map h :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution.sentence_map_comp g h s

/-- Packing commutes with relabelling as equality of typed syntax. -/
theorem packSentence_map (g : P ⟶ Q) (s : FlatInstitution.Sentence P) :
    packSentence (s.map g) = (packSentence s).map g :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution.packSentence_map g s

/-- With one unreachable self-loop, changing its parameter type from unit
to empty changes the written flat sentence while leaving its packed syntax
equal. -/
theorem packSentence_not_injective (P : FlatInstitution.Signature.{u, v} κ) :
    ¬ Function.Injective (packSentence (P := P)) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution.packSentence_not_injective P

variable [AtomValues κ] (Events : Type u → Type u)

theorem packingCorridor_natural (g : P ⟶ Q) :
    FlatInstitution.corridor Events g ≫ packingCorridor Events Q =
      packingCorridor Events P ≫ corridor Events g :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution.packingCorridor_natural Events g

/-- Packing preserves and reflects satisfaction in each shared model. -/
theorem packing_satisfaction (M : Model (κ := κ) Events P.Instr) (s : FlatInstitution.Sentence P) :
    (room Events P).Sat (Discrete.mk M) (packSentence s) ↔ FlatInstitution.Satisfies Events M s :=
  (packingCorridor Events P).sat (Discrete.mk M) s

/-- Semantic consequence between translated sentences is exact because
every flat model is the model component of a packed model. -/
theorem packing_entails_iff (Γ : Set (FlatInstitution.Sentence P)) (φ : FlatInstitution.Sentence P) :
    (FlatInstitution.room Events P).Entails Γ φ ↔
      (room Events P).Entails (packSentence '' Γ) (packSentence φ) :=
  (packingCorridor Events P).entails_map_iff (fun M => ⟨M, rfl⟩) Γ φ

/-- The packed institution uses the same reduct functors as the flat one. -/
@[expose] def roomFunctor (A : Ty κ := Silmaril.unit) : FlatInstitution.Signature.{u, v} κ ⥤ Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  obj P := room Events P A
  map g := corridor Events g A
  map_id P := Room.hom_ext (funext Sentence.map_id) (FlatInstitution.reductFunctor_id Events P)
  map_comp g h := Room.hom_ext (funext (Sentence.map_comp g h)) (FlatInstitution.reductFunctor_comp Events g h)

@[expose] def institution (κ : Type (u + 1)) [AtomValues κ] (A : Ty κ := Silmaril.unit) :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨FlatInstitution.Signature.{u, v} κ, roomFunctor Events A⟩

/-- Packing translates sentences over the identity signature functor and
leaves each model unchanged. -/
@[expose] def packingComorphism (κ : Type (u + 1)) [AtomValues κ] :
    Inst.CoHom (FlatInstitution.institution.{u, v} Events κ) (institution.{u, v} Events κ) where
  Φ := 𝟭 _
  ρ := { app := packingCorridor Events, naturality := fun {_ _} g => packingCorridor_natural Events g }

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.PackedInstitution
