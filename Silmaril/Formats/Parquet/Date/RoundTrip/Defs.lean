module

public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs
public import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs

/-! # Common logical observations for the checked Date32 conversion profiles -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.RoundTrip

/-- One logical Date32 field and its indexed nullable signed epoch-day lists.
An empty inner list is an explicit empty batch or group. -/
structure Observation where
  name : String
  nullable : Bool
  batches : List Arrow.DateStream.Writer.Column
  deriving DecidableEq, Repr

def Observation.ipc (observation : Observation) : Arrow.DateStream.Stream :=
  Arrow.DateStream.Writer.observation observation.name observation.nullable observation.batches

/-- The checked logical observation of a Parquet DATE file. Read every footer
index from the same retained snapshot, preserving explicit empty groups. -/
def ParquetObserves (limits : Date.Limits) (wire : Bytes) (observation : Observation) : Prop :=
  ∃ checked groups, Date.openChecked limits wire = .ok checked ∧
    (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups ∧
    observation = ⟨checked.binding.leaf.name, checked.binding.leaf.repetition == some .optional,
      groups.map (·.date32Slots)⟩

end Silmaril.Formats.Parquet.Date.RoundTrip
