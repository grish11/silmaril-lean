module

import Silmaril.Formats.Parquet.Int96.Mixed.File.Events.Thms

open Silmaril.Formats.Parquet.Int96.Mixed.File

#print axioms Events.metadata_exact
#print axioms Events.schema_field
#print axioms Events.narrowSlot_exact
#print axioms Events.narrowSlot_error_iff
#print axioms Events.narrowSlots_exact
#print axioms Events.narrowSlots_first_error
#print axioms Events.batch_slots
#print axioms Events.slotsAt_source_error
#print axioms Events.slotsAt_after_read
#print axioms Events.readAll_reference
#print axioms Events.readAll_first_error
