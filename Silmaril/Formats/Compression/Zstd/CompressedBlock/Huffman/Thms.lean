module

public import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CompressedBlock.Huffman.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman

open Silmaril.Formats.Compression.Zstd.Huffman

/-- An accepted body has the exact declared extent and a bounded output,
    with both successor states justified by the wire and execution relations. -/
theorem decode_sound {profile : TreeDescription.Limits} {limits : Limits} {prior : State profile}
    {declaredSize : Nat} {body : List UInt8} {result : Result profile} (accepted : prior.block.tables.Valid)
    (success : decode limits prior declaredSize body = .ok result) :
    body.length = declaredSize ∧ declaredSize ≤ limits.inputCapacity ∧
      result.bytes.length ≤ limits.execution.capacity ∧ result.next.block.Valid limits.window ∧
      BlockWire limits prior body result :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.Huffman.decode_sound accepted success

/-- A valid literal prefix with a failing sequence suffix returns only the
    typed error, including failures after sequence tables have been resolved. -/
theorem decode_suffix_failure {profile : TreeDescription.Limits} {limits : Limits} {prior : State profile}
    {declaredSize : Nat} {body : List UInt8} {parsed : LiteralState.Result profile}
    {reason : CompressedBlock.Error}
    (fits : declaredSize ≤ limits.inputCapacity) (extent : body.length = declaredSize)
    (read : LiteralState.read (literalLimits limits profile) prior.literals body = .ok parsed)
    (failed : Internal.execute limits prior.block parsed.literals parsed.rest = .error reason) :
    decode limits prior declaredSize body = .error (.block reason) :=
  Proofs.Formats.Compression.Zstd.CompressedBlock.Huffman.decode_suffix_failure fits extent read failed

end Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman
