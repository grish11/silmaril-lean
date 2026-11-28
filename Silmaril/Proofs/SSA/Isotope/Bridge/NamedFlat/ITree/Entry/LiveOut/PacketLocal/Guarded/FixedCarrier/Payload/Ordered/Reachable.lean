module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Reachable.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Thms


public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Reachable

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
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
      observeNamedOn target names first second store' literals prim s selected' := by
  rw [l.observe_native_on selected caller store seedValue raw valid,
    r.observe_native_on selected' caller store' seedValue' raw' valid']
  exact Endpoint.checkReachable_sound valid valid' yes prim s

/-- At the supplied caller, a positive verdict is equivalent to refinement
of the original named runs over all deterministic stores of type `Type`. -/
theorem reachable_acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' := by
  simp_rw [l.observe_native_on selected caller store seedValue raw valid,
    r.observe_native_on selected' caller store' seedValue' raw' valid']
  exact Endpoint.checkReachable_accepts_iff valid valid'

/-- A negative verdict is exactly a deterministic counterexample at the
original named endpoints once both exact readbacks have been checked. -/
theorem reachable_rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : Syntax.StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected'  := by
  classical
  have decided := reachable_acceptance_iff l r caller store store' seedValue seedValue'
    raw raw' selected selected' valid valid'
  have supported : (verdict).isSome = true := by
    simp [compareReachable?, Endpoint.checkReachable?, Endpoint.checkAllInterpreters?, valid, valid']
  cases checked : verdict with
  | none => simp [checked] at supported
  | some answer =>
    simp only [checked, Option.some.injEq] at decided ⊢
    simp only [Bool.eq_false_iff, ne_eq, decided, not_forall]

end Compare

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Reachable
