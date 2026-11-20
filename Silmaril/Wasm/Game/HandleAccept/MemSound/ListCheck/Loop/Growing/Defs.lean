module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.IOAccept

/-- The second operand is the minimum page count, not a byte address. Refused growth
traps before imports; successful reservation resets local 1 for the checker loop. -/
def reserve : List Instr :=
  [.localGet ⟨1⟩, .memorySize ⟨0⟩, .intRelOp .i32 (.gt .unsigned), .if_ .empty
    [.localGet ⟨1⟩, .memorySize ⟨0⟩, .intBinOp .i32 .sub, .memoryGrow ⟨0⟩,
      .intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq, .if_ .empty [.unreachable] []] [],
    .intConst .i32 0, .localSet ⟨1⟩]

/-- `check(root, minimumPages)` grows the current memory only when necessary. -/
def mod (ix : ListImports) (pages : InitialPages := InitialPages.one) : Module :=
  { Loop.mod ix pages with funcs := [⟨⟨0⟩, [.i32, .i32], reserve ++ body⟩] }

/-- The persistent memory32 premise needed by the prologue on every export. -/
def Memory32 (store : Store Nat) : Prop :=
  ∃ memory, store.mems = [memory] ∧ memory.type.address = .i32 ∧ memory.pages ≤ 65536

/-- Host answers may write bytes, but must preserve the address width and bounded page
count required by the next reservation. -/
def reply (call : UCall Nat) (answer : UReply) : Prop :=
  Items.itemsReply call answer ∧ (Memory32 call.store → Memory32 answer.store)

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing
