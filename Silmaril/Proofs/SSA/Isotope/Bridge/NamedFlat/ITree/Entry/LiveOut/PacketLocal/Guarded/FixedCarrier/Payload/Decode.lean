module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Decode.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Decode

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack unpack_pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Exits)

theorem constructor_roundtrip {A : Syntax.Ty} (p : Syntax.Payload A) :
    decodeConstructor A (Recognize.encodeValue ULift.up p.val) = some p := by
  obtain ⟨v, h⟩ := p
  induction h with
  | atom h => contradiction
  | unit => rfl
  | pair _ _ ih₁ ih₂ => simp [Recognize.encodeValue, decodeConstructor, ih₁, ih₂]
  | inl _ ih => simp [Recognize.encodeValue, decodeConstructor, ih]
  | inr _ ih => simp [Recognize.encodeValue, decodeConstructor, ih]

private theorem packed_value {A : Syntax.Ty} (p : Packet (Exits A)) :
    (packedReturn p).2 = Recognize.encodeValue ULift.up (pack p).val := by
  rcases p with ⟨i, payload⟩
  fin_cases i <;> rfl

theorem packed_roundtrip {A : Syntax.Ty} (p : Packet (Exits A)) :
    decodePacked (Exits A) (packedReturn p) = some p := by
  change (decodeConstructor _ (packedReturn p).2).map _ = _
  rw [packed_value, constructor_roundtrip, Option.map_some, unpack_pack]

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Decode
