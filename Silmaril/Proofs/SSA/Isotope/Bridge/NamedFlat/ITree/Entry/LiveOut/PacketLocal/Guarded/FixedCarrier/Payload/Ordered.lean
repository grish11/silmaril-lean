module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (Flat)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
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
open PayloadRecognition (Incoming rowTransfer packetValue packetTree unfold_return request_row_transfer named_tree_of_readback roots)

attribute [local instance] requestTypes

theorem eval_fields {Φ : Type} {d : Nat} {hasBit : Bool} (literals : Φ → Option Bool)
    (f : Fields Φ hasBit) (agrees : f.Agrees literals) (tag : Tag) (env : Env Runtime)
    (input : Syntax.Payload (if hasBit then Bit else .unit)) (caller : Syntax.Bindings [Bit]) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up input.val) .unit)) (f.rowAt (d := d) tag).erase =
      pure (tag.natAdd d |>.val, encodeValue ULift.up (f.output.eval (caller.push input)).val) := by
  rcases f with ⟨first, second⟩
  obtain ⟨firstEq, secondEq⟩ := agrees
  cases first <;> cases second <;>
    simp [Fields.rowAt, finishAt, Fields.output, fieldExpr, recordExpr, Flat.erase, Morphism.CaseSSA.erase,
      region, LambdaSSA.Semantics.Interaction.term, rawWithLiterals, extend, PayloadRecognition.Write.Agrees]
      at firstEq secondEq ⊢
  · rfl
  · simp [secondEq]
    cases ‹Bool› <;> rfl
  · simp [firstEq]
    cases ‹Bool› <;> rfl
  · simp [firstEq, secondEq]
    rename_i _ a _ b
    cases a <;> cases b <;> rfl

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {b : Admission P (interface seed names) (fields first second) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool} {states results : Nat}

private theorem eval_block (ck : Checked a op literals) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (p : Packet Incoming) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up p.2.val) .unit))
      ((ck.profile.expected op).block p.1).erase = rowTransfer (ck.profile.endpoint op selected) caller p := by
  rcases p with ⟨i, p⟩
  fin_cases i
  · exact request_row_transfer (P := P) literals op ck.profile.routes ck.profile.bitTag ck.profile.unitTag
      selected (ck.profile.endpoint op selected).output caller p env
  · change _ = pure ((ck.profile.bitTag.natAdd 3).val,
      packetValue ((ck.profile.endpoint op selected).returnPacket caller ⟨1, p⟩ ck.profile.bitTag))
    rw [unfold_return]
    exact eval_fields literals ck.profile.atBit ck.literals_agree.1 _ env p _
  · change _ = pure ((ck.profile.unitTag.natAdd 3).val,
      packetValue ((ck.profile.endpoint op selected).returnPacket caller ⟨2, p⟩ ck.profile.unitTag))
    rw [unfold_return]
    exact eval_fields literals ck.profile.atUnit ck.literals_agree.2 _ env p _

theorem named_tree (ck : Checked a op literals) (selected : Tag → Bool) (caller : Syntax.Payload Bit)
    (store : V → Value Runtime) (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw (rawWithLiterals literals) [names 3, names 4] (fun _ => [first, second]) source store =
      packetTree (ck.profile.endpoint op selected) caller ⟨0, caller⟩ :=
  named_tree_of_readback ck.readback (ck.profile.endpoint op selected) caller caller store rfl seedValue
    (eval_block ck selected caller)

theorem observe_native [DecidableEq P.Instr] (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (codec : Fin results ≃ Packet Outputs) (prim : Syntax.Primitives P.Instr states)
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) (s : Fin states) :
    observeNamed source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s := by
  unfold OrderedLiveOut.observeNamed
  rw [named_tree ck selected caller store seedValue]
  exact observe_roots_native (ck.profile.endpoint op selected) codec caller raw valid prim configs stores
    (packetTree (ck.profile.endpoint op selected) caller) (roots (ck.profile.endpoint op selected) caller)
    (constructorDecoder PayloadType) constructorDecoder_return s

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

theorem acceptance_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        observeNamed source names first second store literals prim s selected ≤
          observeNamed target names first second store' literals prim s selected' := by
  have left (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native l selected caller store seedValue raw valid codec prim configs stores s
  have right (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native r selected' caller' store' seedValue' raw' valid' codec prim configs stores s
  simpa only [← left, ← right] using!
    (l.profile.endpoint op selected).acceptance_iff (r.profile.endpoint op' selected') raw raw' codec
      caller caller' replies configs configs stores valid valid'

theorem rejection_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ observeNamed source names first second store literals prim s selected ≤
          observeNamed target names first second store' literals prim s selected' := by
  have left (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native l selected caller store seedValue raw valid codec prim configs stores s
  have right (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native r selected' caller' store' seedValue' raw' valid' codec prim configs stores s
  simpa only [← left, ← right] using!
    (l.profile.endpoint op selected).rejection_iff (r.profile.endpoint op' selected') raw raw' codec
      caller caller' replies configs configs stores valid valid'

end Comparison

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
