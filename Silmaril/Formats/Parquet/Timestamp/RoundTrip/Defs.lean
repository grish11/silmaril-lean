module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

/-! Checked intermediate observations for Arrow TIMESTAMP → Parquet → Arrow. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.RoundTrip

/-- The emitted leaf at ordinal one recovers the admitted descriptor and one
ordered group of signed nullable ticks per original IPC batch. -/
def ParquetObserves (limits : FromIpc.Limits) (wire : Bytes)
    (stream : Arrow.TimestampStream.Stream) : Prop :=
  ∃ annotation bound groups,
    FromIpc.descriptor stream.binding = .ok annotation ∧
    Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
    FromIpc.Internal.readGroups limits.leaf bound = .ok groups ∧
    FromIpc.Internal.ReadbackMatches ⟨stream, annotation⟩ bound groups

end Silmaril.Formats.Parquet.Timestamp.RoundTrip
