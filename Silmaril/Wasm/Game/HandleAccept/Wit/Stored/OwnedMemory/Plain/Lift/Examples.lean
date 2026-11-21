module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Lift.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Lift.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

def compound : TypeOf :=
  .record [("choice", .option (.prim .u32)), ("items", .list (.prim .u8))]

theorem admitted : Stored.checkSchema compound = .ok () := by kernel_rfl

private abbrev World := List (Except Issue Observed)

private noncomputable def context : LiftLowerContext Mock.mock :=
  { opts := { memory := some 0 }, inst := ⟨0⟩ }

private noncomputable def program (receipts : Bool) (input : Stored.Input) :
    P Mock.mock World (Ret Mock.mock) := do
  let result ← if receipts then
    (fun result => result.map Subtype.val) <$> lift Component.Limits.spec Quirks.none context compound input
  else
    (fun result => (result.map (Observed.ordinary ∘ Subtype.val)).mapError Issue.schema) <$>
      Stored.lift Component.Limits.spec Quirks.none context compound input
  hostSet [result]
  pure .unit

private noncomputable def initial (receipts : Bool) (input : Stored.Input) :
    Machine.Config Mock.mock World where
  store := { CStore.empty with
    core := { mems := [⟨.i32, ⟨#[1, 0, 0, 0, 9, 0, 0, 0, 16, 0, 0, 0, 2, 0, 0, 0, 3, 8]⟩⟩] }
    insts := [{}]
    tasks := [{ ft := ⟨[], none, false⟩, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ status := .running, task := ⟨0⟩ }] }
  host := []
  ctl := [Machine.Activation.ofProg (some ⟨0⟩) (program receipts input)]

private def noReady : HostReady World := fun _ _ => false

private noncomputable def noCalls (_ : Canon.Call Mock.mock) : P Mock.mock World (Ret Mock.mock) :=
  internal "unexpected call during compound lift"

private noncomputable def run (X : Mock.mock.Exec) (receipts : Bool) (input : Stored.Input) :=
  Machine.run noReady noCalls X Machine.Oracle.first 160 (initial receipts input)

private def expected : Observed :=
  Observed.ordinary (.record [.variant 1 (some (Val.u32 9)), .list [.int .u8 3, .int .u8 8]])

theorem memory_lifts_choice_and_list (X : Mock.mock.Exec) (receipts : Bool) :
    let result := run X receipts (.memory 0)
    (result.outcome, result.config.host) = (.resolved, [.ok expected]) := by
  cases receipts <;> (dsimp only; kernel_rfl)

theorem flat_lifts_choice_and_indirect_list (X : Mock.mock.Exec) (receipts : Bool) :
    let result := run X receipts (.flat [.int .i32 1, .int .i32 9, .int .i32 16, .int .i32 2])
    (result.outcome, result.config.host) = (.resolved, [.ok expected]) := by
  cases receipts <;> (dsimp only; kernel_rfl)

theorem wrong_flat_lane_rejects (X : Mock.mock.Exec) (receipts : Bool) :
    let result := run X receipts (.flat [.int .i32 0, .int .i64 0, .int .i32 16, .int .i32 0])
    (result.outcome, result.config.host) = (.resolved, [.error (.schema .flatTypes)]) := by
  cases receipts <;> (dsimp only; kernel_rfl)

theorem bad_flat_discriminant_traps (X : Mock.mock.Exec) (receipts : Bool) :
    let result := run X receipts (.flat [.int .i32 2, .int .i32 0, .int .i32 16, .int .i32 2])
    (result.labels.any (fun label => match label with | .trap .invalidDiscriminant => true | _ => false),
      result.config.host) = (true, []) := by
  cases receipts <;> (dsimp only; kernel_rfl)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Lift.Examples
