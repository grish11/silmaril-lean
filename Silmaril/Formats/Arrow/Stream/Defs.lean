module

public import Silmaril.Formats.Arrow.Layout.Defs

/-! A finite in-memory stream profile. The first message is a bodyless schema.
The remaining frames are record batches followed by explicit modern EOS. -/

namespace Silmaril.Formats.Arrow

public structure Stream where
  fields : List Field
  batches : List (BatchFrame fields)

/-- Read a batch suffix at a known frame boundary. The accumulator holds the
batches already consumed, in reverse order. -/
@[expose] public def Stream.readBatches (limits : Limits) (input : KBytes) (fields : List Field) :
    Nat → Nat → List (BatchFrame fields) → Except Error (List (BatchFrame fields))
  | remaining, offset, reversed => do
    match ← readEnvelope limits input offset with
    | .eos =>
      if offset + 8 = input.len then return reversed.reverse
      else throw (.malformed .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.limit .batches)
      | fuel + 1 =>
        let message ← readMessage limits (input.slice (offset + 8) size)
        let .recordBatch metadata := message.header | throw (.malformed .schemaOrder)
        let bodyStart := offset + 8 + size
        let body ← readBody limits input bodyStart message.bodyLength
        let batch ← validateBatch fields metadata body
        readBatches limits input fields fuel (bodyStart + message.bodyLength) (batch :: reversed)

/-- Decode an entire stream into its schema and body-backed batch metadata.
Offsets and limits are checked against the actual byte carrier. -/
@[expose] public def readStream (limits : Limits) (input : KBytes) : Except Error Stream := do
  if !input.wf then throw (.malformed .source)
  let .metadata size ← readEnvelope limits input 0 | throw (.malformed .schemaOrder)
  let message ← readMessage limits (input.slice 8 size)
  let .schema fields := message.header | throw (.malformed .schemaOrder)
  if message.bodyLength ≠ 0 then throw (.malformed .bodyLength)
  let batches ← Stream.readBatches limits input fields limits.batches (8 + size) []
  return ⟨fields, batches⟩

end Silmaril.Formats.Arrow
