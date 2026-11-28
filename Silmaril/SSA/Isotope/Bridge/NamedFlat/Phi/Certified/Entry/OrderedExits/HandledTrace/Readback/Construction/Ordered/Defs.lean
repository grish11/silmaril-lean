module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs

/-! # Construct public rows at the profiles of an ordered φ readback -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)
universe u

/-- Structural types retain their constructors and order in the finite
public codec. Atomic base types require a separate finite representation. -/
def Readback.packetType {κ : Type u} : Ty κ → Option PacketType
  | .base _ => none
  | .empty => some .empty
  | .unit => some .unit
  | .product left right => do return .product (← Readback.packetType left) (← Readback.packetType right)
  | .coprod left right => do return .coprod (← Readback.packetType left) (← Readback.packetType right)

def Readback.packetProfile {κ : Type u} {n : Nat} (types : Fin n → Ty κ) :
    Option {profile : Fin n → PacketType // ∀ i, packetType (types i) = some (profile i)} := do
  let entries ← Readback.tabulateDependent n
      (A := fun i => {pkt : PacketType // packetType (types i) = some pkt}) fun i =>
    match packetType (types i) with
    | none => none
    | some a => some ⟨a, rfl⟩
  return ⟨fun i => (entries i).val, fun i => (entries i).property⟩

variable {κ V Reg K : Type 1} [DecidableEq V] [DecidableEq Reg] [DecidableEq K]
  {P : LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution.Signature.{0, 0} κ}
  {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

/-- The generated interface is tied to the actual block and ordered
live-out types of the admitted readback. -/
structure PublicReadback (a : Admission P I fields C) (signature : PrimitiveSignature P.Instr) where
  lowered : NamedFlat.Entry.Reverse.Lowered I fields a.code
  packets : Fin (Versioning.compile (Phi.OrderedExits.lower a.source)).blocks.length → PacketType
  exits : Fin I.exits.length → PacketType
  packetTypes : ∀ i, Readback.packetType (a.internal i) = some (packets i)
  exitTypes : ∀ i, Readback.packetType ((NamedFlat.Entry.LiveOut.exitInterface I fields).external i) = some (exits i)
  compiled : Readback.Constructed signature packets exits a.code

/-- Traverse the exact readback at the profiles recovered from the ordered
admission. Runtime capture agreement and primitive codec agreement are
separate premises of `Readback.Provenance.alignment`. -/
def Admission.constructPublic [DecidableEq P.Instr] (a : Admission P I fields C)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields a.code)
    (signature : PrimitiveSignature P.Instr) : Option (PublicReadback a signature) :=
  match Readback.packetProfile a.internal,
      Readback.packetProfile (NamedFlat.Entry.LiveOut.exitInterface I fields).external with
  | some packets, some exits =>
    (Readback.construct signature packets.val exits.val a.code).map fun result =>
      ⟨lowered, packets.val, exits.val, packets.property, exits.property, result⟩
  | _, _ => none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
