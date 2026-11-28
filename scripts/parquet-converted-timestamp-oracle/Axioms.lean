module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

open Silmaril.Formats.Parquet.Timestamp

#print axioms readMetadataWith_selects
#print axioms annotationWith_modern
#print axioms annotationWith_converted
#print axioms Leaf.bindWith_sound
#print axioms Leaf.openLeafWith_sound
#print axioms Leaf.Events.readBound_reference
#print axioms Leaf.Events.ToIpc.openBoundWith_sound
#print axioms Leaf.Events.ToIpc.convertWith_readback
#print axioms Leaf.Events.ToIpc.convertWith_first_error
#print axioms Leaf.Events.readBound_first_error
