module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet

/-! # Exactness of the positional packet encoding -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Silmaril.Isotope.LambdaSSA.Region (packedExitValue)

variable {L : List Syntax.Ty}

theorem unpack_pack (p : Packet L) : unpack (pack p) = p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.unpack_pack p

theorem pack_unpack (a : Packed L) : pack (unpack a) = a :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.pack_unpack a

theorem pack_value (p : Packet L) : (pack p).val = packedExitValue p.1 p.2.val :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.pack_value p

/-- The semantic dependent sum matches the native right-associated tag type. -/
def packetEquiv (L : List Syntax.Ty) : Packet L ≃ Packed L :=
  ⟨pack, unpack, unpack_pack, pack_unpack⟩

theorem Packet.raw_injective : Function.Injective (Packet.raw (L := L)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.packet_raw_injective

/-- Erasing the typing proof preserves the exact label and payload. -/
def Packet.erase : Packet L ↪ (Fin L.length × Value Unit) :=
  ⟨Packet.raw, Packet.raw_injective⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
