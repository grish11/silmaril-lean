module

import Silmaril.Formats.Parquet.Int96.File.Thms

open Silmaril.Formats.Parquet.Int96.File

#print axioms openFile_sound
#print axioms readGroup_eq_readColumn
#print axioms readGroup_wire
#print axioms readAll_sound
#print axioms readAll_complete
#print axioms readAll_first_error
