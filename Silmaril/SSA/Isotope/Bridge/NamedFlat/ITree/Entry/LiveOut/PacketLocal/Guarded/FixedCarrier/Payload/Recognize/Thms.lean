module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Recognize.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Recognize

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit requestTypes interface encodeValue)
open LiveBit (PayloadType rawWithLiterals)

attribute [local instance] requestTypes

/-- The typed constructor payload returns unchanged at its ordered tag. -/
theorem decode_return (p : Packet Outputs) :
    LiveBit.decode (packedReturn p) = some (p.1, p.2.val) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.decode_return p

/-- Unfold feedback once at a request and through the pending exit at a
return. The equation tracks every typed reply, including backedges. -/
theorem roots {Φ : Type} (g : Endpoint (Recognize.signature Φ) Incoming PayloadType)
    (caller : Syntax.Payload (Incoming.get g.control.entry)) :
    RootAgrees g caller (packetTree g caller) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.roots g caller

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed reg : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (LiveBit.fields reg) source}
  {b : Admission P (interface seed names) (LiveBit.fields reg) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool} {states results : Nat}

local notation "I" => (interface (κ := κ) seed names)

/-- The admitted table's checked readback supplies the entry and all local
steps of the payload-aware tree. The original run projects the final register. -/
theorem Checked.named_tree (ck : Checked a op literals) (selected : Tag → Bool) (caller : Syntax.Payload Bit)
    (store : V → Value Runtime) (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw (rawWithLiterals literals) (I).exits (fun _ => [reg]) source store =
      packetTree (ck.profile.endpoint op selected) caller ⟨0, caller⟩ :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.named_tree
    ck selected caller store seedValue

/-- Exact native readback and successful named recognition give the same
decorated observations on the supplied deterministic carrier. -/
theorem Checked.observe_native [DecidableEq P.Instr] (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (codec : Fin results ≃ Packet Outputs) (prim : Syntax.Primitives P.Instr states)
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) (s : Fin states) :
    LiveBit.observeNamed source names reg store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.observe_native
    ck selected caller store seedValue raw valid codec prim configs stores s

section Comparison

variable [DecidableEq P.Instr]
  (l : Checked a op literals) (r : Checked b op' literals)
  (caller caller' : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller'.val)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (codec : Fin results ≃ Packet Outputs) (replies : ReplyEnumeration (Recognize.signature P.Instr))
  (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)

include seedValue seedValue' valid valid'

/-- With both named and native checks accepted, the verdict compares the
original named runners under a shared interpreter and initial machine state. -/
theorem acceptance_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        LiveBit.observeNamed source names reg store literals prim s selected ≤
          LiveBit.observeNamed target names reg store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.acceptance_iff
    l r caller caller' store store' seedValue seedValue' raw raw' selected selected' codec replies configs stores valid valid'

/-- With both readbacks accepted, a negative verdict is exactly a semantic
counterexample on the original named runners. Unsupported syntax gives none. -/
theorem rejection_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ LiveBit.observeNamed source names reg store literals prim s selected ≤
          LiveBit.observeNamed target names reg store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition.rejection_iff
    l r caller caller' store store' seedValue seedValue' raw raw' selected selected' codec replies configs stores valid valid'

end Comparison

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition
