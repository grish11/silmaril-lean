module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Checked.Thms

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.CheckedExamples

open Silmaril.Formats Silmaril.Wasm.Game.Accept Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Component

def signature (types : List PTy) : WitSig := ⟨Unit, fun _ => types, fun _ => .fixed 0⟩

def tagOf (types : List PTy) (_ : BitVec 32) : Option (signature types).Tag := some ()

def node (bytes : List UInt8) (payload : BitVec 32 := 0) (count : BitVec 32 := 0) : Callout :=
  ⟨("wit", "node"), [.i32 0, .i32 payload, .i32 0, .i32 count], some bytes.toByteArray⟩

def issue {Value : Type} : Except NodeIssue Value → Option NodeIssue
  | .ok _ => none
  | .error reason => some reason

def owningNode (types : List PTy) (rt : Own.RT) (o : Callout) :=
  Own.checkedOwnNode (signature types) (tagOf types) {} rt o

def plainNode (types : List PTy) (o : Callout) := checkedNode (signature types) (tagOf types) {} o

def aliasTable : Own.RT := fun handle =>
  if handle = 1 ∨ handle = 2 then some ⟨3, 77, true⟩ else none

theorem inactive_own_rejects :
    issue (owningNode [.option (.own 3)] aliasTable (node [0, 0, 0, 0, 0, 0, 0, 0])) =
      some (.payload (.nestedOwn 3)) := rfl

theorem empty_borrow_list_rejects :
    issue (plainNode [.list (.borrow 4)] (node [0, 0, 0, 0, 0, 0, 0, 0])) =
      some (.payload (.storedBorrow 4)) := rfl

theorem inactive_own_no_success_projection :
    Callout.witNode (signature [.option (.own 3)]) (tagOf [.option (.own 3)])
      (node [0, 0, 0, 0, 0, 0, 0, 0]) = none := rfl

theorem inactive_own_no_raw_resolution :
    Own.resolveOp (signature [.option (.own 3)]) aliasTable ⟨(), (none, ())⟩ = none := by
  rw [← Own.resolveOpChecked_toOption]
  rfl

theorem plain_own_requires_table :
    issue (plainNode [.own 3] (node [1, 0, 0, 0])) = some (.payload (.requiresResourceTable 3)) := rfl

theorem async_kinds_reject :
    checkPayload (Ref := Empty) .ownFields true (.variant [("hidden", some (.future none))]) =
      .error .future ∧
    checkPayload (Ref := Empty) .ownFields true (.result none (some (.stream none))) =
      .error .stream ∧
    checkPayload (Ref := Empty) .ownFields true (.list .errorContext) = .error .errorContext :=
  ⟨rfl, rfl, rfl⟩

theorem invalid_abi_modes_reject :
    checkNodeMode { address := .i64 } = .error (.addressWidth .i64) ∧
    checkNodeMode { encoding := .utf16 } = .error (.stringEncoding .utf16) ∧
    checkNodeMode { encoding := .latin1Utf16 } = .error (.stringEncoding .latin1Utf16) ∧
    checkNodeMode { passing := .flat } = .error .flatPayload ∧
    checkNodeMode { asynchronous := true } = .error .asyncCall :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem memory64_store_rejects :
    issue (checkedCallout ("wit", "node") 0
      ⟨0, { mems := [⟨⟨.i64, ⟨0, none⟩⟩, ByteArray.empty⟩] }, []⟩) =
      some (.addressWidth .i64) := rfl

theorem bad_memory_rejects :
    issue (plainNode [.u32] (node [1, 0, 0, 0] 1)) = some .unalignedPayload ∧
    issue (plainNode [.u32] (node [1])) = some .payloadOutOfBounds ∧
    issue (plainNode [] (node [] 0 0x4000000)) = some .childrenTooLong ∧
    issue (plainNode [.string] (node [8, 0, 0, 0, 0, 0, 0, 16])) = some .badPayload ∧
    issue (plainNode [.list .u32] (node [8, 0, 0, 0, 0, 0, 0, 4])) = some .badPayload :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem invalid_moves_reject :
    issue (owningNode [.own 3] aliasTable (node [4, 0, 0, 0])) = some (.resource (.unknown 4)) ∧
    issue (owningNode [.own 3] (aliasTable.killAll [1]) (node [1, 0, 0, 0])) =
      some (.resource (.dead 1)) ∧
    issue (owningNode [.own 4] aliasTable (node [1, 0, 0, 0])) =
      some (.resource (.wrongType 1 4 3)) ∧
    issue (owningNode [.own 3, .own 3] aliasTable (node [1, 0, 0, 0, 1, 0, 0, 0])) =
      some (.resource .duplicate) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_rep_distinct_handles :
    owningNode [.own 3, .own 3] aliasTable (node [1, 0, 0, 0, 2, 0, 0, 0]) =
      .ok ((⟨(), ((77 : Nat), (77 : Nat), ())⟩, []), aliasTable.killAll [1, 2]) := rfl

theorem schema_error_precedes_move :
    issue (owningNode [.own 3, .option (.own 3)] aliasTable (node [4, 0, 0, 0])) =
      some (.payload (.nestedOwn 3)) := rfl

theorem invalid_later_field_leaves_first_live :
    let types := [.own 3, .own 3]
    Own.nodeResult (signature types) aliasTable
      (owningNode types aliasTable (node [1, 0, 0, 0, 4, 0, 0, 0])) =
        (.error (.resource (.unknown 4)), aliasTable) := rfl

theorem rejected_retry_retains_earlier_move :
    let table := aliasTable.killAll [1]
    Own.nodeResult (signature [.own 3]) table (owningNode [.own 3] table (node [1, 0, 0, 0])) =
      (.error (.resource (.dead 1)), table) := rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.CheckedExamples
