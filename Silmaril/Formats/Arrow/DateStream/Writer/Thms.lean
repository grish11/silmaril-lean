module

public import Silmaril.Formats.Arrow.DateStream.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.Writer.RoundTrip

public section

namespace Silmaril.Formats.Arrow.DateStream.Writer

open Silmaril.Formats.DateInterop

/-- The preflight size is the exact padded Schema metadata extent. -/
theorem schemaMetadata_size (name : String) (nullable : Bool) :
    (Internal.schemaMetadata name nullable).len = Internal.schemaSize name :=
  Proofs.Formats.Arrow.DateStream.Writer.schemaMetadata_size name nullable

/-- Successful emission preserves the logical DATE field, nullable slots
and the nested batch lists, including empty batches. -/
theorem emit_readback {limits : ObservationLimits} {name : String} {nullable : Bool}
    {batches : List Column} {wire : KBytes} (written : emit limits name nullable batches = .ok wire) :
    DateStream.read limits.ipc wire = .ok (observation name nullable batches) :=
  Proofs.Formats.Arrow.DateStream.Writer.emit_readback written

/-- The civil observation recovers every original signed Date32 word. -/
theorem observation_words (name : String) (nullable : Bool) (batches : List Column) :
    (observation name nullable batches).batches.map
        (List.map (fun slot => slot.bind Date32.ofCivil?)) = batches :=
  Proofs.Formats.Arrow.DateStream.Writer.observation_words name nullable batches

end Silmaril.Formats.Arrow.DateStream.Writer
