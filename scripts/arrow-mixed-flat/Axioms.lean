module

import Silmaril.Formats.Arrow.MixedFlat.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms

open Silmaril.Formats.Arrow.MixedFlat

#print axioms Assignment.exact
#print axioms Group.shape
#print axioms Plan.ordered_disjoint
#print axioms Plan.buffer_exact
#print axioms Plan.readGroups_fields
#print axioms readBatch_shape

#print axioms Stream.readSchemaFrame_iff
#print axioms Stream.readRecord_iff
#print axioms Stream.readBatches_iff
#print axioms Stream.read_iff
#print axioms Stream.RecordWire.ranges
#print axioms Stream.RecordWire.decode
#print axioms Stream.read_batch_results
