module

import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms

open Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc

#print axioms readSource_ok_iff
#print axioms readSource_eos
#print axioms readSource_open_error
#print axioms readSource_first_error
#print axioms packValue_wf
#print axioms packValue_octets
#print axioms batches_octets
#print axioms batches_row_counts
#print axioms observeIpc_of_read
