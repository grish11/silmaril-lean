module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

/-! # Decode a constructor payload before ordered exit selection -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet Packed unpack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Exits)

/-- Check an erased constructor value at the supplied atom-free type. -/
def decodeConstructor : (A : Syntax.Ty) → Value Runtime → Option (Syntax.Payload A)
  | .unit, .unit => some ⟨.unit, .unit⟩
  | .product A B, .pair a b => do
    let x ← decodeConstructor A a
    let y ← decodeConstructor B b
    return ⟨.pair x.val y.val, .pair x.property y.property⟩
  | .coprod A _, .inl a => (decodeConstructor A a).map fun x => ⟨.inl x.val, .inl x.property⟩
  | .coprod _ B, .inr b => (decodeConstructor B b).map fun y => ⟨.inr y.val, .inr y.property⟩
  | _, _ => none

/-- Decode the existing packed sum, then unpack its dependent tag and payload. -/
def decodePacked (L : List Syntax.Ty) : Transfer Runtime → Option (Packet L)
  | (0, value) => (decodeConstructor (LambdaSSA.Region.packedExitType L) value).map (unpack (L := L))
  | _ => none

def constructorDecoder (A : Syntax.Ty) : ExitDecoder :=
  fun out => (decodePacked (Exits A) out).map fun p => (p.1, p.2.val)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
