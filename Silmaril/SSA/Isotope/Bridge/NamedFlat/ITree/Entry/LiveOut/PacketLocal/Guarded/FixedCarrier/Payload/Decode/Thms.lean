module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Decode.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Decode

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Exits)

/-- Reuse the native dependent packet decoder at the two original ordered exits. -/
theorem decodePacked_return {A : Syntax.Ty} (p : Packet (Exits A)) :
    decodePacked (Exits A) (packedReturn p) = some p :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Decode.packed_roundtrip p

theorem constructorDecoder_return {A : Syntax.Ty} (p : Packet (Exits A)) :
    constructorDecoder A (packedReturn p) = some (p.1, p.2.val) := by
  simp only [constructorDecoder, decodePacked_return, Option.map_some]

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
