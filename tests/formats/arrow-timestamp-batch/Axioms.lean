module

import Silmaril.Formats.Arrow.TimestampBatch.Thms
import Silmaril.Formats.Arrow.Metadata.Thms
import Silmaril.Formats.Arrow.DateBatch.Thms
import Silmaril.Formats.Arrow.DateStream.Thms

open Silmaril.Formats.Arrow

#print axioms SchemaReader.TimestampUnit.normalize_eq_ok_iff
#print axioms SchemaReader.TimestampUnit.normalize_eq_error_iff
#print axioms TimestampBatch.bindSchema_iff
#print axioms TimestampBatch.batchView_layout
#print axioms TimestampBatch.decodeBatch_sound
#print axioms TimestampBatch.readBatch_binds
#print axioms DateBatch.decode_iff
#print axioms DateStream.readSchema_iff
