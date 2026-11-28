module

import Silmaril.Formats.ColumnarTimestamp.Thms

open Silmaril.Formats.ColumnarTimestamp

#print axioms toInt64_eq_ok_iff
#print axioms toInt64_eq_precisionLoss_iff
#print axioms toInt64_eq_outOfRange_iff
#print axioms Arrow.Metadata.kind_eq_utcInstant_iff
#print axioms Arrow.Metadata.parquet_kind
#print axioms Arrow.Metadata.encode_decode
#print axioms Arrow.Metadata.toParquet_eq_ok_iff
#print axioms Arrow.Metadata.toParquet_roundtrip
#print axioms Parquet.Metadata.kind_eq_utcInstant_iff
#print axioms Parquet.Metadata.arrow_kind
#print axioms Parquet.Metadata.encode_decode
#print axioms Parquet.Metadata.toArrow_eq_ok_iff
#print axioms Parquet.Metadata.toArrow_roundtrip
#print axioms LocalDateTime.toTicks?_ofTicks
#print axioms LocalDateTime.ofTicks_toTicks?
