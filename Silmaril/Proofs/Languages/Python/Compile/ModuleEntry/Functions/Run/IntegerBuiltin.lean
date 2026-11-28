module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module (ListHeap)
open Core.Module.SeededCall (Namespace)

theorem readSequenceLength_ok_iff (space : Namespace) (length : Nat) (value : Int) :
    readSequenceLength space length = .ok value ↔
      space.lookupGlobal "len" = some (.builtin .len) ∧ value = Int.ofNat length := by
  cases found : space.lookupGlobal "len" with
  | none => simp [readSequenceLength, found]
  | some callee =>
    cases callee with
    | builtin identity => cases identity <;> simp [readSequenceLength, found, eq_comm]
    | _ => simp [readSequenceLength, found]

theorem readOrdinal_ok_iff (space : Namespace) (point : UInt32) (valid : point.toNat < 0x110000)
    (value : Int) :
    readIntegerBuiltin space (.ordinal point valid) = .ok value ↔
      space.lookupGlobal "ord" = some (.builtin .ord) ∧ value = Int.ofNat point.toNat := by
  cases found : space.lookupGlobal "ord" with
  | none => simp [readIntegerBuiltin, found]
  | some callee =>
    cases callee with
    | builtin identity => cases identity <;> simp [readIntegerBuiltin, found, eq_comm, Core.Module.SeededCall.Request.decode]
    | helper descriptor =>
      cases descriptor <;> simp [readIntegerBuiltin, found, Core.Module.SeededCall.Request.decode]
    | _ => simp [readIntegerBuiltin, found, Core.Module.SeededCall.Request.decode]

theorem run_assertIntegerBuiltin {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : IntegerBuiltinTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertIntegerBuiltin test :: rest) lists =
      let result := readIntegerBuiltin space test.argument
      let receipt : CallEvent := ⟨test.argument.name, ⟨result.map .int, none⟩⟩
      match result.bind (checkIntegerBuiltinResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest lists
        { tail with calls := receipt :: tail.calls } := by
  simp only [runInstructionsIn, effectWithLists, effect, assertIntegerBuiltin]
  cases (readIntegerBuiltin space test.argument).bind (checkIntegerBuiltinResult space test) <;> rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.IntegerBuiltin
