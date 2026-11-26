module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Binding

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf

/-- Both the checked schema and the original footer select the same leaf. -/
theorem bind_sound {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat} {bound : Bound}
    (accepted : bind limits snapshot ordinal = .ok bound) :
    bound.snapshot = snapshot ∧ bound.ordinal = ordinal ∧ ordinal ≠ 0 ∧
      Internal.isFlat snapshot.metadata.schema = true ∧
      snapshot.metadata.schema[ordinal]? = some bound.binding.leaf ∧
      Timestamp.readMetadata limits ordinal (Internal.metadataBytes snapshot) = .ok bound.binding ∧
      Timestamp.Page.leafLevels? bound.binding.leaf = some bound.levels :=
  Proofs.Formats.Parquet.Timestamp.Leaf.bind_sound accepted

/-- The retained source is the checked snapshot of the supplied bytes. -/
theorem openLeaf_sound {limits : Snapshot.Limits} {source : Bytes} {ordinal : Nat} {bound : Bound}
    (accepted : openLeaf limits source ordinal = .ok bound) :
    Snapshot.check (Failure := Unit) limits source = .ok bound.snapshot ∧
      bind limits.footer bound.snapshot ordinal = .ok bound :=
  Proofs.Formats.Parquet.Timestamp.Leaf.openLeaf_sound accepted

/-- The selected chunk is the corresponding INT64 entry in the requested
group, with the annotated leaf's path and a bounded, disjoint byte span. -/
theorem selectChunk_sound {limits : Limits} {bound : Bound} {index : Nat} {chunk : Chunk}
    (selected : selectChunk limits bound index = .ok chunk) :
    bound.snapshot.groupAt index = some chunk.group ∧
      chunk.group.columns[bound.ordinal - 1]? = some chunk.column ∧
      chunk.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      chunk.column.metadata.physicalType = .int64 ∧
      chunk.column.metadata.numValues = chunk.group.numRows ∧
      chunk.column.metadata.codec = 0 ∧
      chunk.group.numRows.toNat ≤ limits.maxRows ∧
      Parquet.Page.columnSpan bound.snapshot.footer.start chunk.column.metadata = some chunk.span ∧
      Internal.disjoint bound.snapshot index (bound.ordinal - 1) chunk.span = true :=
  Proofs.Formats.Parquet.Timestamp.Leaf.selectChunk_sound selected

/-- The returned slots are the descriptor's exact pointwise interpretation
of the original nullable INT64 slots, in framed chunk order. -/
theorem readGroup_sound {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (accepted : readGroup limits bound index = .ok slots) :
    ∃ chunk frames raw,
      selectChunk limits bound index = .ok chunk ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames ∧
      Parquet.Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
      List.Forall₂ (PhysicalFrame limits.page bound chunk.column.metadata.codec) frames raw ∧
      slots = raw.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.readGroup_sound accepted

end Silmaril.Formats.Parquet.Timestamp.Leaf
