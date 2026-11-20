module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-- Reject a word whose last byte falls outside the addressable memory32 range.
The two comparisons in `body` use precisely these bounds. -/
def Addressable (base index : BitVec 32) : Prop :=
  index.toNat ≤ 1073741823 ∧ base.toNat ≤ 4294967292 - 4 * index.toNat

/-- Locals are the input handle, index, base and scaled offset. Each iteration
rereads `items`; no handle is fetched from a vector left behind by a child reply.
The reader contract must relate every reread to the same denoted list. -/
def iteration : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 0, .call ⟨0⟩,
   .localGet ⟨1⟩, .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩,
   .intRelOp .i32 .eq, .if_ .empty [.localGet ⟨0⟩, .call ⟨2⟩, .return_] [],
   .localGet ⟨1⟩, .intConst .i32 1073741823, .intRelOp .i32 (.gt .unsigned),
   .if_ .empty [.unreachable] [],
   .localGet ⟨1⟩, .intConst .i32 4, .intBinOp .i32 .mul, .localSet ⟨3⟩,
   .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .intConst .i32 4294967292, .localGet ⟨3⟩, .intBinOp .i32 .sub,
   .intRelOp .i32 (.gt .unsigned), .if_ .empty [.unreachable] [],
   .localGet ⟨2⟩, .localGet ⟨3⟩, .intBinOp .i32 .add, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .call ⟨1⟩,
   .localGet ⟨1⟩, .intConst .i32 1, .intBinOp .i32 .add, .localSet ⟨1⟩, .br ⟨0⟩]

/-- The loop starts with the zero-initialized index in local 1. -/
def body : List Instr := [.loop .empty iteration]

/-- Initial page count within the memory32 limit. -/
abbrev InitialPages := { count : Nat // count ≤ 65536 }

def InitialPages.one : InitialPages := ⟨1, by decide⟩

def memoryType (pages : InitialPages) : MemoryType :=
  ⟨.i32, ⟨⟨pages.val, by have := pages.property; omega⟩, none⟩⟩

/-- Variable-length memory checker with the same three imports as `listMod`. -/
def mod (ix : ListImports) (pages : InitialPages := InitialPages.one) : Module :=
  { listMod ix with memories := [memoryType pages], funcs := [⟨⟨1⟩, [.i32, .i32, .i32], body⟩] }

def listsOf (kind : Set SymStrBytesSExp) : Set SymStrBytesSExp :=
  {tree | ∃ children : List SymStrBytesSExp, (∀ child ∈ children, child ∈ kind) ∧
    tree = SExp.ofList children}

/-- A necessary length bound for the memory32 checker: at most `2 ^ 30` four-byte
words fit in its address range. This does not assert that a host can represent every
list at that limit or that its replies use any particular base address. -/
def boundedListsOf (kind : Set SymStrBytesSExp) : Set SymStrBytesSExp :=
  {tree | ∃ children : List SymStrBytesSExp, children.length ≤ 2 ^ 30 ∧
    (∀ child ∈ children, child ∈ kind) ∧ tree = SExp.ofList children}

/-- The loop has checked exactly the prefix before `index` of the tree held by `root`.
It retains neither the last memory image nor the handles it contained. -/
def CheckedPrefix (kind : Set SymStrBytesSExp)
    (env : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)
    (root : BitVec 32) (children : List SymStrBytesSExp) (index : Nat) : Prop :=
  env root = some (SExp.ofList children) ∧ index ≤ children.length ∧
    ∀ pos (bound : pos < children.length), pos < index → children[pos] ∈ kind

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
