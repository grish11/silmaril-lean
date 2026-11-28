module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Reachable.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Reachable


public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (Payload.Endpoint)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes encodeValue)

attribute [local instance] requestTypes

universe v


variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  [DecidableEq P.Instr] {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {b : Admission P (interface seed names) (fields first second) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool}

section Compare

variable (l : Checked a op literals) (r : Checked b op' literals)
  (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)

local notation "verdict" => compareReachable? (some l) (some r) raw raw' selected selected' caller

include seedValue seedValue' valid valid'

/-- At the supplied caller, acceptance is sound in every state universe. -/
theorem reachable_acceptance_sound {σ : Type v} (yes : verdict = some true)
    (prim : Syntax.StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected ≤
      observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Reachable.reachable_acceptance_sound
    l r caller store store' seedValue seedValue' raw raw' selected selected' valid valid' yes prim s

/-- At the supplied caller, a positive verdict is equivalent to refinement
of the original named runs over all deterministic stores of type `Type`. -/
theorem reachable_acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Reachable.reachable_acceptance_iff l r caller store store' seedValue seedValue'
    raw raw' selected selected' valid valid'

/-- A negative verdict is exactly a deterministic counterexample at the
original named endpoints once both exact readbacks have been checked. -/
theorem reachable_rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' :=
  Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Reachable.reachable_rejection_iff l r caller store store' seedValue seedValue'
    raw raw' selected selected' valid valid'

end Compare

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
