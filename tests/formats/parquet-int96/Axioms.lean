module

import Silmaril.Formats.Parquet.Int96.Thms

open Silmaril.Formats.Parquet.Int96.Payload

#print axioms encode_length
#print axioms decode_encode
#print axioms encode_of_decode
#print axioms decode_eq_none_iff
#print axioms ofEpochDay_eq_some_iff
#print axioms ofTicks_eq_none_iff
#print axioms toTicks_ofTicks
#print axioms ofTicks_toTicks
#print axioms toInt64_eq_ok_iff
#print axioms ofGregorian_toGregorian
#print axioms toGregorian_ofGregorian
