module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Examples

open Silmaril.Formats Silmaril.Wasm.Game.Accept Silmaril.Wasm.Execution.Core

def signature (types : List PTy) : WitSig := ⟨Unit, fun _ => types, fun _ => .fixed 0⟩

def node (types : List PTy) (rt : RT) (bytes : List UInt8) :=
  checkedNode (signature types) (fun _ => some ()) {} rt
    ⟨("wit", "node"), [.i32 0, .i32 0, .i32 0, .i32 0], some bytes.toByteArray⟩

def nested : List PTy := [.record [("first", .option (.own 3)), ("rest", .list (.own 3))]]

def memory (index : UInt8) : List UInt8 :=
  [1, 0, 0, 0, 1, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0, index, 0, 0, 0]

def table : RT := fun handle => if handle = 1 ∨ handle = 2 then some ⟨3, 77, true⟩ else none

theorem record_option_list_moves :
    node nested table (memory 2) =
      .ok ((⟨(), ((some (77 : Nat), ([(77 : Nat)], ())), ())⟩, []), table.killAll [2, 1]) := rfl

theorem record_option_list_duplicate_rejects :
    node nested table (memory 1) = .error (.resource .duplicate) := rfl

theorem later_failure_does_not_commit_reservations :
    nodeResult (signature nested) table (node nested table (memory 4)) =
      (.error (.resource (.unknown 4)), table) := rfl

theorem nested_borrow_still_rejects :
    node [.list (.borrow 3)] table [0, 0, 0, 0, 0, 0, 0, 0] =
      .error (.payload (.storedBorrow 3)) := rfl

def nestedPair : List PTy := [.fixedList (.own 3) 2]

theorem fixed_list_moves :
    (node nestedPair table [1, 0, 0, 0, 2, 0, 0, 0]).map
      (fun ((value, children), updated) =>
        (value.2.1.toList, children, (updated 1).map ResEntry.live, (updated 2).map ResEntry.live)) =
      .ok ([(77 : Nat), (77 : Nat)], [], some false, some false) := by
  kernel_rfl

def variant : List PTy := [.variant [("handle", some (.own 3)), ("unit", none)]]

theorem inactive_variant_leaves_table :
    node variant table [1, 0, 0, 0, 4, 0, 0, 0] =
      .ok ((⟨(), (.inr (.inl ()), ())⟩, []), table) := rfl

def runPair (last : UInt8) : Except NodeIssue RT := do
  let (_, updated) ← node [.option (.own 3)] table [1, 0, 0, 0, 1, 0, 0, 0]
  let (_, updated) ← node [.option (.own 3)] updated [1, 0, 0, 0, last, 0, 0, 0]
  return updated

theorem repeated_calls_disjoint_moves : runPair 2 = .ok ((table.killAll [1]).killAll [2]) := rfl

theorem repeated_calls_cannot_move_same_slot : runPair 1 = .error (.resource (.dead 1)) := rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Examples
