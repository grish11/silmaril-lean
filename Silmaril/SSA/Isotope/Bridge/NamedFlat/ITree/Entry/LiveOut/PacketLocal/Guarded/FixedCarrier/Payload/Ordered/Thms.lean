module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes encodeValue)
open LiveBit (rawWithLiterals)
open PayloadRecognition (Incoming packetTree)

attribute [local instance] requestTypes

/-- The scoped return row evaluates the original ordered fields. -/
theorem Fields.eval_row_at {Φ : Type} {d : Nat} {hasBit : Bool} (literals : Φ → Option Bool)
    (f : Fields Φ hasBit) (agrees : f.Agrees literals) (tag : Tag) (env : LambdaSSA.Semantics.Env Runtime)
    (input : Syntax.Payload (if hasBit then Bit else .unit)) (caller : Syntax.Bindings [Bit]) :
    LambdaSSA.Semantics.Interaction.region (LiveBit.rawWithLiterals literals)
        (LambdaSSA.Semantics.extend env (.pair (Recognize.encodeValue ULift.up input.val) .unit)) (f.rowAt (d := d) tag).erase =
      pure (tag.natAdd d |>.val, Recognize.encodeValue ULift.up (f.output.eval (caller.push input)).val) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.eval_fields
    literals f agrees tag env input caller


/-- The scoped return row evaluates the original ordered fields. -/
theorem Fields.eval_row {Φ : Type} {hasBit : Bool} (literals : Φ → Option Bool)
    (f : Fields Φ hasBit) (agrees : f.Agrees literals) (tag : Tag) (env : LambdaSSA.Semantics.Env Runtime)
    (input : Syntax.Payload (if hasBit then Bit else .unit)) (caller : Syntax.Bindings [Bit]) :
    LambdaSSA.Semantics.Interaction.region (LiveBit.rawWithLiterals literals)
        (LambdaSSA.Semantics.extend env (.pair (Recognize.encodeValue ULift.up input.val) .unit)) (f.row tag).erase =
      pure (tag.natAdd 3 |>.val, Recognize.encodeValue ULift.up (f.output.eval (caller.push input)).val) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.eval_fields
    literals f agrees tag env input caller


variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {b : Admission P (interface seed names) (fields first second) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool} {states results : Nat}

/-- The exact named lowering computes the ordered record from its two final
register slots. The packet tree uses the same typed replies and backedges. -/
theorem Checked.named_tree (ck : Checked a op literals) (selected : Tag → Bool) (caller : Syntax.Payload Bit)
    (store : V → Value Runtime) (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw (rawWithLiterals literals) [names 3, names 4] (fun _ => [first, second]) source store =
      packetTree (ck.profile.endpoint op selected) caller ⟨0, caller⟩ :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.named_tree
    ck selected caller store seedValue

/-- Interpret the checked native endpoint and the original mutable projection
under the same caller, interpreter and exit-selection predicate. -/
theorem Checked.observe_native [DecidableEq P.Instr] (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (codec : Fin results ≃ Packet Outputs) (prim : Syntax.Primitives P.Instr states)
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) (s : Fin states) :
    observeNamed source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.observe_native
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

/-- Accepted readbacks give the same positive verdict as the order on the
original named observations at every state in the supplied carrier. -/
theorem acceptance_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        observeNamed source names first second store literals prim s selected ≤
          observeNamed target names first second store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.acceptance_iff
    l r caller caller' store store' seedValue seedValue' raw raw' selected selected' codec replies configs stores valid valid'

/-- A negative verdict between accepted endpoints has exactly the stated
semantic witness under a shared interpreter. -/
theorem rejection_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ observeNamed source names first second store literals prim s selected ≤
          observeNamed target names first second store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.rejection_iff
    l r caller caller' store store' seedValue seedValue' raw raw' selected selected' codec replies configs stores valid valid'

end Comparison

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
