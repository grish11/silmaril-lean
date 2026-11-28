module

public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Defs

/-! Pull events over one retained, immutable strict Arrow IPC file. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull

open Silmaril.Relational

/-- The cursor retains the original carrier and the unread footer entries.
It carries the ordinal and accepted row count of its completed prefix. -/
inductive Cursor : Scan.Schema MixedFlat.Field Unit → Type where
  | at (input : KBytes) (fields : List MixedFlat.Field) (blocks : List FileBlock)
      (ordinal rows : Nat) : Cursor (schema fields)

def Cursor.callCount {signature : Scan.Schema MixedFlat.Field Unit} : Cursor signature → Nat
  | .at _ _ blocks _ _ => blocks.length + 1

/-- Open checks the strict index. A call to next decodes one footer entry or
reports EOS at the end. A failed call keeps its original ordinal and cause. -/
def reader (limits : MixedFlat.Limits) :
    Arrow.Events.BatchReader KBytes MixedFlat.Field (fun _ => Cell) Error Cursor where
  openInput input :=
    ((MixedFlat.File.readIndex limits.observation.ipc input).mapError Error.file).map fun index =>
      ⟨schema index.footer.fields, .at input index.footer.fields index.footer.blocks 0 0⟩
  next
    | .at _ _ [] _ _ => .ok none
    | .at input fields (block :: rest) n rows =>
      (readStep limits input fields n rows block).map fun (total, batch) =>
        some (batch, .at input fields rest (n + 1) total)
  close _ := .ok ()

/-- Collect the opened cursor with enough calls to observe EOS. The generic
pull driver keeps completed batches when the next call fails. -/
def readAll (limits : MixedFlat.Limits) (input : KBytes) : Stream :=
  ((reader limits).openInput input).map fun ⟨signature, cursor⟩ =>
    ⟨signature, Arrow.Events.BatchReader.read.pull (reader limits) signature cursor.callCount cursor []⟩

/-- Concrete reasons for stopping at a footer entry. Wire errors come from
the strict decoder. Budget errors follow a successfully decoded candidate. -/
def StopsAt (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (n rows : Nat) (block : FileBlock) (error : Error) : Prop :=
  (∃ cause, MixedFlat.File.readRecord limits input fields block = .error cause ∧
    error = .file (.batch n cause)) ∨
  ∃ observed cause, MixedFlat.File.readRecord limits input fields block = .ok observed ∧
    Body.checkBudget limits.observation fields.length (rows + observed.rowCount) = .error cause ∧
    error = .budget n cause

end Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull
