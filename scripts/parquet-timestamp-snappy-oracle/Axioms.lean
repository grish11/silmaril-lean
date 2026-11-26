module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms selectChunk_sound
#print axioms PhysicalFrame.preparedWire
#print axioms readGroup_sound
#print axioms Events.readBound_reference
#print axioms Events.ToIpc.convertWith_readback
#print axioms Events.ToIpc.convertWith_first_error
