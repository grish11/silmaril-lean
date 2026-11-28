module

public import Silmaril.Semantics.ExactITree.Defs

/-! A one-byte file fixture for exact positioned and cursor-relative read lowering. -/

@[expose] public section

namespace Silmaril.Process.ExactITree.File

open Silmaril.Elgot.ITree Silmaril.Elgot.ITree.Exact CategoryTheory

/-- Requests for one fixed readable handle, each asking for at most one byte. -/
inductive FileEvent : Type → Type
  | pread (offset : Nat) : FileEvent (Option UInt8)
  | read : FileEvent (Option UInt8)

/-- A decoded success with the optional byte actually copied into the buffer.
An empty copy-out denotes EOF in this fixture. -/
structure CopyOut where
  buffer : Nat
  byte : Option UInt8

inductive ABIEvent : Type → Type
  | pread64 (fd buffer offset : Nat) : ABIEvent CopyOut
  | read (fd buffer : Nat) : ABIEvent CopyOut

abbrev source : Signature := ⟨FileEvent⟩
abbrev target : Signature := ⟨ABIEvent⟩

/-- Resolve the fixed handle to descriptor 3 and use a private backed buffer at 4096. -/
def lowering : source ⟶ target where
  exchange
    | .pread offset => ⟨_, .pread64 3 4096 offset, CopyOut.byte⟩
    | .read => ⟨_, .read 3 4096, CopyOut.byte⟩

inductive Stop where
  | unsupported

/-- The file is immutable environment data. The store is the open-description cursor. -/
abbrev profile : Profile := ⟨List UInt8, Nat, UInt8, Stop⟩

def readAt (file : List UInt8) (buffer offset after : Nat) : Completion profile CopyOut :=
  .reply ⟨buffer, file[offset]?⟩ after []

def readCursor (file : List UInt8) (buffer cursor : Nat) : Completion profile CopyOut :=
  readAt file buffer cursor (cursor + file[cursor]?.isSome.toNat)

def complete (ignorePosition : Bool) (file : List UInt8) (cursor : Nat) {R : Type} :
    ABIEvent R → Completion profile R
  | .pread64 fd buffer offset =>
    if fd = 3 ∧ buffer = 4096 then
      if ignorePosition then readCursor file buffer cursor else readAt file buffer offset cursor
    else .stop .unsupported none []
  | .read fd buffer =>
    if fd = 3 ∧ buffer = 4096 then readCursor file buffer cursor else .stop .unsupported none []

def kernel (ignorePosition : Bool) : Kernel profile target :=
  fun file cursor {_} e answer => complete ignorePosition file cursor e = answer

def contents : List UInt8 := [0x41, 0x42]

abbrev ReadPair := Option UInt8 × Option UInt8

def sentence : Sentence profile source where
  Return := ReadPair
  test := vis (FileEvent.pread 1) fun first => vis FileEvent.read fun second => ret (first, second)
  pre file cursor := file = contents ∧ cursor = 0
  post _ _ obs :=
    match obs with
    | .prefix _ => True
    | .finished _ (.returned values _) => values = (some 0x42, some 0x41)
    | _ => False

end Silmaril.Process.ExactITree.File
