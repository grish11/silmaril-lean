module

import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Thms
meta import Silmaril.Formats.Arrow.TimestampStream.FromCsv.Defs

namespace Silmaril.Formats.Arrow.TimestampStream.FromCsv

open ToCsv (schemaOf)
open Silmaril.Formats.Relational.NamedTable (schemaMatches)

private def absent : TimestampBatch.Binding := ⟨"time", true, ⟨.nanosecond, none⟩⟩
private def presentEmpty : TimestampBatch.Binding := ⟨"time", true, ⟨.nanosecond, some ""⟩⟩

#guard !(schemaMatches (schemaOf absent) (schemaOf presentEmpty))
#guard (checkSchema {} (schemaOf absent) KBytes.empty).isOk == false

#print axioms checkSchema_sound
#print axioms emit_readback
#print axioms convert_readback

end Silmaril.Formats.Arrow.TimestampStream.FromCsv
