module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Institution.Thms

/-! # Rooms for ordered packed programs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.PackedInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room)

universe u v

variable {κ : Type (u + 1)} {P Q : FlatInstitution.Signature.{u, v} κ}

/-- Compare two typed singleton programs from the same input type to
one ordered external exit profile. The programs need not be in the image of packing. -/
structure Sentence (P : FlatInstitution.Signature.{u, v} κ) (A : Ty κ := Silmaril.unit) where
  exits : Nat
  external : Fin exits → Ty κ
  left : Program P.Instr A (Region.packedExitType (List.ofFn external))
  right : Program P.Instr A (Region.packedExitType (List.ofFn external))

/-- Relabel the written singleton programs without changing their endpoints. -/
def Sentence.map {A : Ty κ} (s : Sentence P A) (g : P ⟶ Q) : Sentence Q A :=
  ⟨s.exits, s.external, s.left.map g.toSignatureMap g.types, s.right.map g.toSignatureMap g.types⟩

/-- Pack both actual typed flat tables at their common external profile. -/
def packSentence (s : FlatInstitution.Sentence P) : Sentence P :=
  ⟨s.exits, s.external, Program.ofCFG s.left.typed, Program.ofCFG s.right.typed⟩

variable [AtomValues κ] (Events : Type u → Type u)

/-- Use the flat institution's model category and the existing packed order. -/
def room (P : FlatInstitution.Signature.{u, v} κ) (A : Ty κ := Silmaril.unit) :
    Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := Sentence P A
  Mod := (FlatInstitution.room Events P).Mod
  Sat M s := M.as.Satisfies s.left s.right

/-- Primitive relabelling acts contravariantly on the shared models. -/
def corridor (g : P ⟶ Q) (A : Ty κ := Silmaril.unit) : room Events P A ⟶ room Events Q A where
  sen s := s.map g
  mod := FlatInstitution.reductFunctor Events g
  sat M s := satisfies_map_iff M.as g.toSignatureMap g.types g.bottom s.left s.right

/-- The model component is the identity. Flat satisfaction already uses
the denotations of these two packed programs. -/
def packingCorridor (P : FlatInstitution.Signature.{u, v} κ) :
    FlatInstitution.room Events P ⟶ room Events P where
  sen := packSentence
  mod := 𝟭 _
  sat _ _ := Iff.rfl

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.PackedInstitution
