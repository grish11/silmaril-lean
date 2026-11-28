module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Defs
public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs

/-! # Exact Zstandard compressed bodies with stateful Huffman literals

RFC 8878 §§3.1.1.2.4–3.1.1.5. The caller provides the exact type-2
body, the window, and state from accepted blocks. The entry point is
independent of frame parsing and works from a dictionary-free initial state.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman

open Silmaril.Formats.Compression.Zstd.Huffman

structure State (profile : TreeDescription.Limits) where
  literals : LiteralState.State profile
  block : CompressedBlock.State

def State.initial (profile : TreeDescription.Limits) : State profile :=
  ⟨LiteralState.State.empty profile, CompressedBlock.State.initial⟩

structure Result (profile : TreeDescription.Limits) where
  bytes : List UInt8
  next : State profile

inductive Error where
  | block (reason : CompressedBlock.Error)
  | literals (reason : LiteralState.Error)
  deriving DecidableEq, Repr

def literalLimits (limits : Limits) (profile : TreeDescription.Limits) : LiteralSection.Limits :=
  ⟨limits.inputCapacity, limits.execution.capacity, profile⟩

/-- The literal prefix leaves exactly the sequence section. Only the
    executed block publishes the checked literal and sequence transitions. -/
def BlockWire {profile : TreeDescription.Limits} (limits : Limits) (prior : State profile)
    (body : List UInt8) (result : Result profile) : Prop :=
  ∃ (parsed : LiteralState.Result profile) (literalBytes : List UInt8),
    LiteralState.Wire (literalLimits limits profile) prior.literals body parsed ∧
    body = literalBytes ++ parsed.rest ∧ literalBytes.length = parsed.consumed ∧
    parsed.consumed ≤ limits.inputCapacity ∧
    parsed.literals.expand.length = parsed.literals.size ∧
    parsed.literals.size ≤ limits.execution.capacity ∧
    result.next.literals = parsed.next ∧
    Internal.SequenceWire limits prior.block parsed.literals parsed.rest ⟨result.bytes, result.next.block⟩

/-- Check the body extent first, then decode literals and execute the complete
    sequence suffix. Both candidate table states are returned on success. -/
def decode {profile : TreeDescription.Limits} (limits : Limits) (prior : State profile)
    (declaredSize : Nat) (body : List UInt8) : Except Error (Result profile) := do
  (Internal.checkExtent limits declaredSize body).mapError Error.block
  let parsed ← (LiteralState.read (literalLimits limits profile) prior.literals body).mapError Error.literals
  let executed ← (Internal.execute limits prior.block parsed.literals parsed.rest).mapError Error.block
  return ⟨executed.bytes, ⟨parsed.next, executed.next⟩⟩

end Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman
