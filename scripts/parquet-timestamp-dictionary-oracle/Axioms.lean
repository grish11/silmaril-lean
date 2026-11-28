module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms

open Silmaril.Formats.Parquet.Timestamp.Leaf

#print axioms selectChunkWith_sound
#print axioms Dictionary.readEntries_wire
#print axioms Dictionary.planData_wire
#print axioms Dictionary.checkGroup_wire
#print axioms Dictionary.readGroup_wire
#print axioms Dictionary.data_decodes
#print axioms Dictionary.readBound_reference
#print axioms Dictionary.convert_readback
#print axioms Dictionary.convert_first_error
