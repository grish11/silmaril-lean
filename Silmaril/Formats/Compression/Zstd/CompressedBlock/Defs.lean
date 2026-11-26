module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs
public import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
public import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs

/-! # Bounded Zstandard compressed block payloads

RFC 8878 §§3.1.1.2.4–3.1.1.5. The caller supplies an exact type-2 body
and the window and state from previously accepted blocks.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CompressedBlock

open CheckedFrame.Rle (History)

structure Limits where
  window : Nat
  inputBytes : Nat
  outputBytes : Nat
  commands : Nat
  deriving DecidableEq, Repr

def Limits.inputCapacity (limits : Limits) : Nat := min limits.inputBytes (min limits.window 131072)

def Limits.execution (limits : Limits) : Sequence.Limits := ⟨limits.window, limits.outputBytes⟩

/-- Each command emits a match of at least three bytes. -/
def Limits.sequences (limits : Limits) : SequenceTables.Limits :=
  ⟨limits.inputCapacity, min limits.commands (limits.execution.capacity / 3)⟩

structure State where
  tables : SequenceTables.Repeat.State
  history : History
  deriving DecidableEq, Repr

def State.initial : State := ⟨SequenceTables.Repeat.State.empty, History.initial⟩

def State.Valid (state : State) (window : Nat) : Prop :=
  state.tables.Valid ∧ state.history.recent.size ≤ window ∧ state.history.offsets.Valid

/-- Advance past bytes from an already checked raw or RLE block. Those
    block types change history while keeping the tables and repeat offsets. -/
def State.advancePlain (state : State) (window : Nat) (bytes : List UInt8) : State :=
  ⟨state.tables, state.history.advance window bytes state.history.offsets⟩

structure Result where
  bytes : List UInt8
  next : State
  deriving DecidableEq, Repr

inductive Error where
  | inputLimit
  | sizeMismatch
  | literals (reason : LiteralBlock.Error)
  | tables (reason : SequenceTables.Repeat.Error)
  | sequences (reason : SequenceDecode.Error)
  | execution (reason : Sequence.Error)
  deriving DecidableEq, Repr

namespace Internal

/-- Check the exact compressed body extent before either literal reader runs. -/
def checkExtent (limits : Limits) (declaredSize : Nat) (body : List UInt8) : Except Error Unit :=
  if limits.inputCapacity < declaredSize then .error .inputLimit
  else if body.drop declaredSize ≠ [] then .error .sizeMismatch
  else if body.length ≠ declaredSize then .error .sizeMismatch
  else .ok ()

/-- The sequence wire, bounded execution and successor shared by both literal profiles. -/
def SequenceWire (limits : Limits) (prior : State) (literals : LiteralBlock.Literals)
    (sequenceBytes : List UInt8) (result : Result) : Prop :=
  ∃ resolvedSection commands emitted suffix offsets,
    SequenceTables.Repeat.SectionWire prior.tables sequenceBytes resolvedSection ∧
    SequenceTables.Repeat.StateUpdate prior.tables resolvedSection result.next.tables ∧
    SequenceDecode.PayloadWire resolvedSection commands ∧
    commands.length = resolvedSection.count ∧ commands.length ≤ limits.sequences.sequences ∧
    Sequence.Runs limits.window commands prior.history.recent.toList literals.expand
      prior.history.offsets emitted suffix offsets ∧
    result.bytes = emitted ++ suffix ∧
    result.next.history = prior.history.advance limits.window result.bytes offsets

/-- Resolve and execute the complete sequence suffix before returning state. -/
def execute (limits : Limits) (prior : State) (literals : LiteralBlock.Literals)
    (sequenceBytes : List UInt8) : Except Error Result := do
  let (resolvedSection, tables) ←
    (SequenceTables.Repeat.resolve limits.sequences prior.tables sequenceBytes).mapError Error.tables
  let commands ← (SequenceDecode.readResolved resolvedSection).mapError Error.sequences
  let executed ← (Sequence.execute limits.execution prior.history.recent literals.expand
    prior.history.offsets commands).mapError Error.execution
  return ⟨executed.bytes, ⟨tables, prior.history.advance limits.window executed.bytes executed.offsets⟩⟩

end Internal

/-- The exact literal and sequence sections, their bounded execution, and
    the state produced from the executed output and selected tables. -/
def BlockWire (limits : Limits) (prior : State) (body : List UInt8) (result : Result) : Prop :=
  ∃ literals sequenceBytes resolvedSection commands emitted suffix offsets,
    LiteralBlock.LiteralsWire body literals sequenceBytes ∧
    literals.size ≤ limits.execution.capacity ∧
    SequenceTables.Repeat.SectionWire prior.tables sequenceBytes resolvedSection ∧
    SequenceTables.Repeat.StateUpdate prior.tables resolvedSection result.next.tables ∧
    SequenceDecode.PayloadWire resolvedSection commands ∧
    commands.length = resolvedSection.count ∧ commands.length ≤ limits.sequences.sequences ∧
    Sequence.Runs limits.window commands prior.history.recent.toList literals.expand
      prior.history.offsets emitted suffix offsets ∧
    result.bytes = emitted ++ suffix ∧
    result.next.history = prior.history.advance limits.window result.bytes offsets

/-- Decode precisely the declared compressed body. Check the wire extent and
    literal size before expansion. A successor is returned only after both
    the reverse stream and the bounded execution succeed. -/
def decode (limits : Limits) (prior : State) (declaredSize : Nat) (body : List UInt8) :
    Except Error Result := do
  Internal.checkExtent limits declaredSize body
  let (literals, sequenceBytes) ← (LiteralBlock.parseLiterals limits.execution.capacity body).mapError
    Error.literals
  Internal.execute limits prior literals sequenceBytes

end Silmaril.Formats.Compression.Zstd.CompressedBlock
