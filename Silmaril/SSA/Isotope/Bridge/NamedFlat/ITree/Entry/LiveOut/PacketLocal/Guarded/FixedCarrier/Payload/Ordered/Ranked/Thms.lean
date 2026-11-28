module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Ranked.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Ranked

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes encodeValue)
open PayloadRecognition (Incoming)

attribute [local instance] requestTypes

universe v

/-- The accepted constructor-bit and unit layout has a fixed exhaustive inventory. -/
@[noinline] def configurations : ConfigurationEnumeration Incoming :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.configurations

/-- The native reply signature is the same constructor sum at every opcode. -/
@[noinline] def replyPackets {Φ : Type} : ReplyEnumeration (Recognize.signature Φ) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.replyPackets

theorem output_left_inv : Function.LeftInverse outputEncode outputDecode :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.output_left_inv

theorem output_right_inv : Function.RightInverse outputEncode outputDecode :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.output_right_inv

/-- Two ordered positions and two constructor bits give eight exact result codes. -/
@[expose] def outputCodes : Fin 8 ≃ Packet Outputs where
  toFun := outputDecode
  invFun := outputEncode
  left_inv := output_left_inv
  right_inv := output_right_inv

/-- In this profile entry rank holds exactly when the bit reply goes to the
terminal bit block. Both unit replies already go to the unit terminal. -/
theorem control_rank {Φ : Type} (p : Profile Φ) (op : Φ) (selected : Tag → Bool) :
    let g := (p.endpoint op selected).control
    (g.entryCheck = true ↔ p.routes.destination 0 ≠ 0) ∧
      g.ranks.get g.entry = if p.routes.destination 0 = 0 then none else some 1 :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.control_rank
    p op selected

/-- Specializing the existing one-ranked cutoff to this readback gives two stores. -/
theorem cutoff_two {Φ : Type} (p q : Profile Φ) (op op' : Φ) (selected selected' : Tag → Bool)
    (ranked : (p.endpoint op selected).control.entryCheck = true ∨ (q.endpoint op' selected').control.entryCheck = true) :
    (p.endpoint op selected).control.rankedCutoff (q.endpoint op' selected').control = 2 :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.cutoff_two
    p q op op' selected selected' ranked

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  [DecidableEq P.Instr] {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {b : Admission P (interface seed names) (fields first second) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool} {results : Nat} {σ : Type v}

/-- Exact readback gives equality with the original named weak-tree observer
for arbitrary deterministic stores, including selected UB. -/
theorem Checked.observe_native_on (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (prim : Syntax.StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.native_observation
    ck selected caller store seedValue raw valid prim s

/-- The arbitrary-store observer specializes to the existing finite
observer on any admitted pair of readbacks. -/
theorem Checked.observe_fin_eq {states : Nat} (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (prim : Syntax.Primitives P.Instr states)
    (stores : LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch.StateInventory states)
    (s : Fin states) :
    observeNamedOn source names first second store literals prim s selected =
      observeNamed source names first second store literals prim s selected :=
  (ck.observe_native_on selected caller store seedValue raw valid prim s).trans
    (ck.observe_native selected caller store seedValue raw valid outputCodes prim configurations stores s).symm

section Compare

variable (l : Checked a op literals) (r : Checked b op' literals)
  (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (codec : Fin results ≃ Packet Outputs) (replies : ReplyEnumeration (Recognize.signature P.Instr))
  (configs : ConfigurationEnumeration Incoming)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)
  (ranked : (l.profile.endpoint op selected).control.entryCheck = true ∨
    (r.profile.endpoint op' selected').control.entryCheck = true)

local notation "verdict" => compareRanked? (some l) (some r) raw raw' selected selected' codec caller replies configs

include seedValue seedValue' valid valid' ranked

/-- The one-ranked verdict is sound in every store universe. -/
theorem ranked_acceptance_sound (yes : verdict = some true) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected ≤
      observeNamedOn target names first second store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.acceptance_sound
    l r caller store store' seedValue seedValue' raw raw' selected selected' codec replies configs
    valid valid' ranked yes prim s

/-- At the supplied caller, the one-ranked verdict decides arbitrary-store
deterministic refinement on the original named endpoints. -/
theorem ranked_acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.acceptance_iff
    l r caller store store' seedValue seedValue' raw raw' selected selected' codec replies configs valid valid' ranked

/-- A rejected one-ranked verdict gives an arbitrary-store refutation at
the original named observations. Exact readback and rank gate the verdict. -/
theorem ranked_rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked.rejection_iff
    l r caller store store' seedValue seedValue' raw raw' selected selected' codec replies configs valid valid' ranked

end Compare

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
