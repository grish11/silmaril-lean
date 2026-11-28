module

public import Silmaril.Formats.Parquet.Footer.Validation.Defs

/-! Entry points for the exact, typed plaintext footer reader. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Footer

open ThriftCompact

structure Limits where
  maxFooterBytes : Nat := 8 * 1024 * 1024
  compact : Traversal.Limits := {}
  varintMode : VarintMode := .canonical

inductive Error where
  | framing (error : FramingError)
  | metadata (error : MetadataError)
  | trailingMetadata
  deriving DecidableEq, Repr

/-- Read exactly one `FileMetaData` from an already bounded metadata slice. -/
def readMetadata (limits : Limits) (source : Bytes) : Except Error Metadata := do
  let (metadata, next) ← (readMetadataPrefix ⟨source, limits.compact, limits.varintMode⟩ 0).mapError .metadata
  if next = source.length then pure metadata else throw .trailingMetadata

/-- Locate and read the advertised footer only. Use `validate` for the separate
schema, row-group and data-interval checks. -/
def readFooter (limits : Limits) (file : Bytes) : Except Error (Span × Metadata) := do
  let span ← (locate limits.maxFooterBytes file).mapError .framing
  let metadata ← readMetadata limits (fileBytes file span.start span.stop)
  pure (span, metadata)

end Silmaril.Formats.Parquet.Footer
