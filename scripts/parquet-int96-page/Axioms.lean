module

import Silmaril.Formats.Parquet.Int96.Page.Thms

open Silmaril.Formats.Parquet.Int96.Page

#print axioms parameters_sound
#print axioms decodeSlots_eq_ok_iff
#print axioms decodeSlots_eq_invalidWord_iff
#print axioms decode_eq_ok_iff
#print axioms decode_eq_invalidWord_iff
#print axioms decode_wire_sound
#print axioms decode_counts
