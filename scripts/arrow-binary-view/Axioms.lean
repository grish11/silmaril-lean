module

import Silmaril.Formats.Arrow.BinaryView.Thms
import Silmaril.Formats.Arrow.BinaryView.Column.Thms
import Silmaril.Formats.Arrow.BinaryView.Batch.Thms
import Silmaril.Formats.Arrow.BinaryView.Schema.Thms
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms

open Silmaril.Formats.Arrow.BinaryView

#print axioms readBinary_iff
#print axioms readBinary_extent
#print axioms readUtf8_iff

#print axioms Column.checkBuffers_iff
#print axioms Column.readBinary_iff
#print axioms Column.readBinary_bounds
#print axioms Column.readUtf8_iff
#print axioms Column.readUtf8_counts

#print axioms BatchMetadata.count_verified
#print axioms Batch.frame_buffer_exact
#print axioms Batch.frame_data_at
#print axioms Batch.readBinary_iff
#print axioms Batch.readUtf8_iff
#print axioms Batch.readUtf8_counts

#print axioms Schema.kind_ofTag_iff
#print axioms Schema.readBatch_binds
#print axioms Schema.readBinary_iff
#print axioms Schema.readUtf8_iff

#print axioms Stream.readSchema_iff
#print axioms Stream.readBatch_iff
#print axioms Stream.readBatches_iff
#print axioms Stream.read_iff
#print axioms Stream.batches_length_le
#print axioms Stream.batch_ranges
