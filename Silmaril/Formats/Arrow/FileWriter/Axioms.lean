module

import Silmaril.Formats.Arrow.FileWriter.Thms
import Silmaril.Formats.Arrow.FooterWriter.Thms
import Silmaril.Formats.Arrow.MetadataWriter.Thms
import Silmaril.Formats.Arrow.StreamWriter.Thms

open Silmaril.Formats.Arrow

#print axioms MetadataWriter.Wire.schemaPayload_wf
#print axioms MetadataWriter.Wire.schemaPayload_size
#print axioms MetadataWriter.Wire.schemaPayload_aligned
#print axioms FooterWriter.serialize_extent
#print axioms FooterWriter.emit_exact
#print axioms FileWriter.packRecords_exact
#print axioms FileWriter.assemble_extent
#print axioms FileWriter.emit_index_exact
#print axioms FileWriter.emit_roundtrip
#print axioms StreamWriter.emitBatchFrame_at
