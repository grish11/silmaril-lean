module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (Flat)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes encodeValue)
open LiveBit (rawWithLiterals)
open PayloadRecognition (Incoming rowTransfer packetValue packetTree unfold_return request_row_transfer
  named_tree_of_self_loops roots)
open Syntax (StatePrimitives)

attribute [local instance] requestTypes

universe v


/-- The written named row decodes its incoming packet and transfers that
same packet to the same label without invoking an instruction. -/
theorem eval_loopRow {Φ : Type} (literals : Φ → Option Bool) (i : Fin 3)
    (value : Value Runtime) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair value .unit)) (loopRow i).erase =
      pure (i.val, .pair value .unit) :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.eval_loop
    literals i value env

/-- A successful seed check gives the exact readback binding equation. -/
theorem matchesCaller_iff (caller : Syntax.Payload Bit) (value : Value Runtime) :
    matchesCaller caller value = true ↔ value = encodeValue ULift.up caller.val :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.caller_iff
    caller value

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {op : P.Instr} {literals : P.Instr → Option Bool}

/-- The original named weak-tree observer agrees with the exact native
readback for every deterministic handler at the supplied typed caller. -/
theorem Checked.observe_native_on [DecidableEq P.Instr] {σ : Type v} (ck : Silent.Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.native_observation
    ck selected caller store seedValue raw valid prim s

/-- The original named runner is the payload-aware tree with certified
self-transfers interpreted as ordinary divergence. -/
theorem Checked.named_tree (ck : Silent.Checked a op literals) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw (rawWithLiterals literals) [names 3, names 4]
      (fun _ => [first, second]) source store =
      packetTree (ck.profile.endpoint op selected) caller ⟨0, caller⟩ :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.named_tree
    ck selected caller store seedValue

section Compare

variable [DecidableEq P.Instr] {target : CFG V K P.Instr}
  {b : Admission P (interface seed names) (fields first second) target}
  {op' : P.Instr} (l : Silent.Checked a op literals) (r : Silent.Checked b op' literals)
  (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)

local notation "g" => l.profile.endpoint op selected
local notation "h" => r.profile.endpoint op' selected'
local notation "verdict" => Silent.compare? (some l) (some r) raw raw' selected selected' caller store store'

/-- After named recognition, an unknown result records a failed caller
binding or exact native readback. -/
theorem compare_none_iff :
    verdict = none ↔ matchesCaller caller (store seed) = false ∨ matchesCaller caller (store' seed) = false ∨
      (g).checkNative raw = false ∨ (h).checkNative raw' = false :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.none_iff
    l r caller store store' raw raw' selected selected'

variable (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)

include seedValue seedValue' valid valid'

/-- Acceptance is sound at the original named observations for any
deterministic handler and state type. -/
theorem compare_acceptance_sound {σ : Type v} (yes : verdict = some true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected ≤
      observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.acceptance_sound
    l r caller store store' raw raw' selected selected' seedValue seedValue' valid valid' yes prim s

/-- For checked endpoints and caller bindings, the cutoff verdict is
equivalent to refinement over all deterministic stores of type `Type`. -/
theorem compare_acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.acceptance_iff
    l r caller store store' raw raw' selected selected' seedValue seedValue' valid valid'

/-- A negative verdict gives a deterministic witness at the original named
observations with the same caller bindings. -/
theorem compare_rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent.rejection_iff
    l r caller store store' raw raw' selected selected' seedValue seedValue' valid valid'

end Compare

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent
