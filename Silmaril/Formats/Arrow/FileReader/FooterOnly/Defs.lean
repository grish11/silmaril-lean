module

public import Silmaril.Formats.Arrow.FileReader.Defs

/-! Opt-in random access to V5 Int32/UTF-8 files with the Schema in the footer. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FileReader.FooterOnly

/-- The first allowed block position follows the six magic bytes and two
padding bytes. Every block is contiguous with the next frame or EOS. -/
structure Index (input : KBytes) where
  span : FileReader.FooterSpan input
  footer : FileFooter
  fits : FileReader.BlocksFit span.start 8 footer.blocks

/-- Check the leading message's kind and extent using the first indexed
window. Later records' metadata and bodies are left for selected reads. -/
def checkFirstRecord (limits : Limits) (input : KBytes) : List FileBlock → Except Error Unit
  | [] => .ok ()
  | block :: _ => do
    let .metadata size ← readEnvelope limits input 8 | throw (.malformed .schemaOrder)
    if 8 + size ≠ block.metadataLength then throw (.malformed .metadataLength)
    let message ← readMessage limits (input.slice 16 size)
    let .recordBatch _ := message.header | throw (.malformed .schemaOrder)
    if message.bodyLength ≠ block.bodyLength then throw (.malformed .bodyLength)

/-- Index a file whose declared Schema is in its footer. Permit contiguous
blocks from byte 8 and require a single modern EOS immediately before the
footer. With no records, EOS occupies bytes 8 through 15. -/
def readIndex (limits : Limits) (input : KBytes) : Except Error (Index input) := do
  let span ← FileReader.readFooterSpan limits input
  let footer ← readFileFooter limits (input.slice span.start span.length)
  if fits : FileReader.BlocksFit span.start 8 footer.blocks then
    let .eos ← readEnvelope limits input (span.start - 8) | throw (.malformed .trailingBytes)
    checkFirstRecord limits input footer.blocks
    return ⟨span, footer, fits⟩
  else
    throw (.malformed .batchLayout)

/-- The shared selected-block reader uses the checked ranges and footer
fields. Its lower bound is the end of this file's eight-byte header. -/
def Index.toFileIndex {input : KBytes} (index : Index input) : FileReader.Index input :=
  ⟨index.span, index.footer, 8, index.fits⟩

def Index.readBatchAt {input : KBytes} (index : Index input) (limits : Limits) (n : Nat) :
    Except Error (Option (BatchFrame index.footer.fields)) :=
  index.toFileIndex.readBatchAt limits n

def Index.readRowsAt {input : KBytes} (index : Index input) (limits : ObservationLimits)
    (n : Nat) : Except Error (Option (List Row)) :=
  index.toFileIndex.readRowsAt limits n

end Silmaril.Formats.Arrow.FileReader.FooterOnly
