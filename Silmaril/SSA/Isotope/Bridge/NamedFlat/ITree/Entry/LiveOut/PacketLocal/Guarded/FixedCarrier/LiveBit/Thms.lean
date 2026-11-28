module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open Recognize (Bit Packets exitPayload guardedTable)

attribute [local instance] Recognize.requestTypes

variable {states : Nat}

/-- The finite comparison retains the projected bit and uses the existing
shaped order for selected exits, faults, and divergence. -/
theorem compare_iff (bits bits' : Tag → Bool) (r t : Result 2 states) :
    compare bits bits' r t = true ↔
      resultWithPayload (fun i => exitPayload (some (bits i))) r ≤
        resultWithPayload (fun i => exitPayload (some (bits' i))) t :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.compare_iff
    bits bits' r t

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed reg : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr} {op op' : P.Instr}
  {a : Admission P (Recognize.interface seed names) (fields reg) source}
  {b : Admission P (Recognize.interface seed names) (fields reg) target}
  {bits bits' : Tag → Bool} {exitOp exitOp' : Tag → P.Instr}

/-- Exact readback ties the constructor assignments to the actual mutable
store projection. The decoder follows the named return at the caller's
version-zero bit and retains the final interpreter state. -/
theorem observeNamed_runFinite (checked : Recognize.Checked a op (fun i => some (exitOp i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (s : Fin states) (selected : Tag → Bool) :
    LiveBit.observeNamed source names reg input literals prim s selected =
      resultWithPayload (fun i => exitPayload (some (bits i)))
        ((withSelectedExits op checked.routes selected).runFinite caller prim configs stores ⟨0, caller⟩ s) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.observeNamed_runFinite
    checked caller input seedValue literals agrees prim configs stores s selected

/-- The exact native control emits its typed exit payload through the
generated continuation. Selection uses the original ordered tag. -/
theorem observeNamed_native [DecidableEq P.Instr]
    (checked : Recognize.Checked a op (fun i => some (exitOp i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op checked.routes).checkNative native = true)
    (s : Fin states) (selected : Tag → Bool) :
    LiveBit.observeNamed source names reg input literals prim s selected =
      Shape.denote (nativeEndpoint native bits selected)
        (Syntax.model prim ((guardedTable op checked.routes).bindings caller)) s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.observeNamed_native
    checked caller input seedValue literals agrees prim configs stores native readback s selected

/-- The existing interpreter restrictions decide refinement of the original
named observers on the supplied finite carrier. -/
theorem acceptance_iff [DecidableEq P.Instr]
    (left : Recognize.Checked a op (fun i => some (exitOp i)))
    (right : Recognize.Checked b op' (fun i => some (exitOp' i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (agrees' : ∀ i, literals (exitOp' i) = some (bits' i))
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool) :
    check? op op' left.routes right.routes native native' bits bits' selected selected'
        caller replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        LiveBit.observeNamed source names reg input literals prim s selected ≤
          LiveBit.observeNamed target names reg input literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.acceptance_iff
    left right caller input seedValue literals agrees agrees' replies configs stores native native' readback readback' selected selected'

/-- Given both exact native readbacks, a negative verdict corresponds
to a counterexample at the original named endpoints. -/
theorem rejection_iff [DecidableEq P.Instr]
    (left : Recognize.Checked a op (fun i => some (exitOp i)))
    (right : Recognize.Checked b op' (fun i => some (exitOp' i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (agrees' : ∀ i, literals (exitOp' i) = some (bits' i))
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool) :
    check? op op' left.routes right.routes native native' bits bits' selected selected'
        caller replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ LiveBit.observeNamed source names reg input literals prim s selected ≤
          LiveBit.observeNamed target names reg input literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.rejection_iff
    left right caller input seedValue literals agrees agrees' replies configs stores native native' readback readback' selected selected'

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit
