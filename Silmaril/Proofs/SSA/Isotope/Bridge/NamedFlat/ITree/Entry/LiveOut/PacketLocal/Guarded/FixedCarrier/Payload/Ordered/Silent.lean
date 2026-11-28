module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent
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
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table)
open Recognize (Bit interface requestTypes encodeValue)
open LiveBit (rawWithLiterals)
open PayloadRecognition (Incoming rowTransfer packetValue packetTree unfold_return request_row_transfer
  named_tree_of_self_loops roots)
open Syntax (StatePrimitives)

attribute [local instance] requestTypes

universe v

theorem eval_loop {Φ : Type} (literals : Φ → Option Bool) (i : Fin 3)
    (value : Value Runtime) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair value .unit)) (loopRow i).erase =
      pure (i.val, .pair value .unit) := by
  simp only [loopRow, Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  rfl

theorem caller_iff (caller : Syntax.Payload Bit) (value : Value Runtime) :
    matchesCaller caller value = true ↔ value = encodeValue ULift.up caller.val := by
  rcases caller with ⟨bit, typed⟩
  cases typed with
  | inl shape =>
    cases shape
    cases value <;> simp [matchesCaller, encodeValue]
    rename_i payload
    cases payload <;> simp
  | inr shape =>
    cases shape
    cases value <;> simp [matchesCaller, encodeValue]
    rename_i payload
    cases payload <;> simp

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed first second : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {op : P.Instr} {literals : P.Instr → Option Bool}

private theorem eval_block (ck : Silent.Checked a op literals) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (p : Packet Incoming) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up p.2.val) .unit))
      ((ck.profile.expected op).block p.1).erase =
      match (ck.profile.endpoint op selected).control.head caller p with
      | .diverge => pure (p.1.val, .pair (encodeValue ULift.up p.2.val) .unit)
      | _ => rowTransfer (ck.profile.endpoint op selected) caller p := by
  rcases p with ⟨i, p⟩
  fin_cases i
  · exact request_row_transfer (P := P) literals op ck.profile.routes 0 1 selected
      (ck.profile.endpoint op selected).output caller p env
  · change region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up p.val) .unit))
        (ck.profile.bit.flat 1).erase =
      match (ck.profile.endpoint op selected).control.head caller ⟨1, p⟩ with
      | .diverge => pure (1, .pair (encodeValue ULift.up p.val) .unit)
      | _ => rowTransfer (ck.profile.endpoint op selected) caller ⟨1, p⟩
    generalize rowEq : ck.profile.bit = row
    have agrees := ck.literals_agree.1
    rw [rowEq] at agrees
    cases row with
    | loop =>
      have head : (ck.profile.endpoint op selected).control.head caller ⟨1, p⟩ = .diverge := by
        unfold Table.head
        rw [show (ck.profile.endpoint op selected).control.row 1 =
          (Silent.Row.loop (Φ := P.Instr) (hasBit := true)).control from
          congrArg Silent.Row.control rowEq]
        rfl
      rw [head]
      exact eval_loop literals 1 (encodeValue ULift.up p.val) env
    | ret tag fields =>
      let g := ck.profile.endpoint op selected
      have head : g.control.head caller ⟨1, p⟩ = .exit tag (selected tag) := by
        unfold Table.head
        rw [show g.control.row 1 = (Silent.Row.ret tag fields).control from
          congrArg Silent.Row.control rowEq]
        rfl
      rw [head]
      change region _ _ (Silent.Row.flat (.ret tag fields) _).erase =
        rowTransfer g caller ⟨1, p⟩
      rw [rowTransfer, head]
      change _ = pure ((tag.natAdd 3).val, packetValue (g.returnPacket caller ⟨1, p⟩ tag))
      rw [unfold_return]
      have output : g.output 1 = fields.output := congrArg Silent.Row.output rowEq
      rw [output]
      exact fields.eval_row literals agrees tag env p (g.control.bindings caller)
  · change region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up p.val) .unit))
        (ck.profile.unit.flat 2).erase =
      match (ck.profile.endpoint op selected).control.head caller ⟨2, p⟩ with
      | .diverge => pure (2, .pair (encodeValue ULift.up p.val) .unit)
      | _ => rowTransfer (ck.profile.endpoint op selected) caller ⟨2, p⟩
    generalize rowEq : ck.profile.unit = row
    have agrees := ck.literals_agree.2
    rw [rowEq] at agrees
    cases row with
    | loop =>
      have head : (ck.profile.endpoint op selected).control.head caller ⟨2, p⟩ = .diverge := by
        unfold Table.head
        rw [show (ck.profile.endpoint op selected).control.row 2 =
          (Silent.Row.loop (Φ := P.Instr) (hasBit := false)).control from
          congrArg Silent.Row.control rowEq]
        rfl
      rw [head]
      exact eval_loop literals 2 (encodeValue ULift.up p.val) env
    | ret tag fields =>
      let g := ck.profile.endpoint op selected
      have head : g.control.head caller ⟨2, p⟩ = .exit tag (selected tag) := by
        unfold Table.head
        rw [show g.control.row 2 = (Silent.Row.ret tag fields).control from
          congrArg Silent.Row.control rowEq]
        rfl
      rw [head]
      change region _ _ (Silent.Row.flat (.ret tag fields) _).erase =
        rowTransfer g caller ⟨2, p⟩
      rw [rowTransfer, head]
      change _ = pure ((tag.natAdd 3).val, packetValue (g.returnPacket caller ⟨2, p⟩ tag))
      rw [unfold_return]
      have output : g.output 2 = fields.output := congrArg Silent.Row.output rowEq
      rw [output]
      exact fields.eval_row literals agrees tag env p (g.control.bindings caller)

theorem named_tree (ck : Silent.Checked a op literals) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw (rawWithLiterals literals) [names 3, names 4]
      (fun _ => [first, second]) source store =
      packetTree (ck.profile.endpoint op selected) caller ⟨0, caller⟩ :=
  named_tree_of_self_loops ck.readback (ck.profile.endpoint op selected) caller caller store rfl seedValue
    (eval_block ck selected caller)

theorem native_observation [DecidableEq P.Instr] {σ : Type v} (ck : Silent.Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s := by
  unfold observeNamedOn
  rw [named_tree ck selected caller store seedValue]
  let g := ck.profile.endpoint op selected
  exact (observe_roots_on g caller prim (packetTree g caller) (roots g caller)
    (constructorDecoder PayloadType) constructorDecoder_return ⟨0, caller⟩ s).trans
      (g.observe_entry_state raw valid caller prim s).symm

section Compare

variable [DecidableEq P.Instr] {target : CFG V K P.Instr}
  {b : Admission P (interface seed names) (fields first second) target}
  {op' : P.Instr} (l : Silent.Checked a op literals) (r : Silent.Checked b op' literals)
  (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)

local notation "g" => l.profile.endpoint op selected
local notation "h" => r.profile.endpoint op' selected'
local notation "verdict" => Silent.compare? (some l) (some r) raw raw' selected selected' caller store store'

theorem none_iff :
    verdict = none ↔ matchesCaller caller (store seed) = false ∨ matchesCaller caller (store' seed) = false ∨
      (g).checkNative raw = false ∨ (h).checkNative raw' = false := by
  cases left : matchesCaller caller (store seed) <;> cases right : matchesCaller caller (store' seed) <;>
    cases nativeLeft : (g).checkNative raw <;> cases nativeRight : (h).checkNative raw' <;>
    simp [Silent.compare?, Endpoint.checkReachable?, Endpoint.checkAllInterpreters?, left, right, nativeLeft, nativeRight]

variable (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)

include seedValue seedValue' in
private theorem compare_eq :
    verdict = (g).checkReachable? (h) raw raw' outputCodes caller caller replyPackets configurations configurations := by
  simp [Silent.compare?, (caller_iff caller _).mpr seedValue, (caller_iff caller _).mpr seedValue']

include seedValue seedValue' valid valid'

theorem acceptance_sound {σ : Type v} (yes : verdict = some true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected ≤
      observeNamedOn target names first second store' literals prim s selected' := by
  rw [compare_eq l r caller store store' raw raw' selected selected' seedValue seedValue'] at yes
  rw [native_observation l selected caller store seedValue raw valid prim s,
    native_observation r selected' caller store' seedValue' raw' valid' prim s]
  exact Endpoint.checkReachable_sound valid valid' yes prim s

theorem acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' := by
  constructor
  · intro yes σ prim s
    exact acceptance_sound l r caller store store' raw raw' selected selected' seedValue seedValue' valid valid' yes prim s
  · intro named
    rw [compare_eq l r caller store store' raw raw' selected selected' seedValue seedValue']
    apply (Endpoint.checkReachable_accepts_iff valid valid').mpr
    intro σ prim s
    simpa only [native_observation l selected caller store seedValue raw valid prim s,
      native_observation r selected' caller store' seedValue' raw' valid' prim s] using! named σ prim s

theorem rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' := by
  classical
  have accepted := acceptance_iff l r caller store store' raw raw' selected selected' seedValue seedValue' valid valid'
  have supported : verdict ≠ none := by
    rw [ne_eq, none_iff]
    simp [(caller_iff caller _).mpr seedValue, (caller_iff caller _).mpr seedValue', valid, valid']
  cases checked : verdict with
  | none => exact (supported checked).elim
  | some answer =>
    simp only [checked, Option.some.injEq] at accepted ⊢
    simp only [Bool.eq_false_iff, ne_eq, accepted, not_forall]

end Compare

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Silent
