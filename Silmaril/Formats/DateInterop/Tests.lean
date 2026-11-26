module

import Silmaril.Formats.DateInterop.Thms
meta import Silmaril.Formats.DateInterop.Defs

/-! Signed endpoints, Gregorian validity, and exact Date64 divisibility. -/

open Silmaril.Formats.DateInterop
open Silmaril.Numeric.Gregorian (CivilDate)

#guard Date32.toCivil (-1) = ⟨1969, 12, 31⟩
#guard Date32.ofCivil? ⟨2000, 2, 29⟩ = some 11016
#guard Date32.ofCivil? ⟨1900, 2, 29⟩ = none
#guard Date32.ofCivil? ⟨0, 2, 29⟩ = some (-719469)
#guard Date32.ofEpochDay? (-2147483648) = some Int32.minValue
#guard Date32.ofEpochDay? 2147483647 = some Int32.maxValue
#guard Date32.ofEpochDay? (-2147483649) = none
#guard Date32.ofEpochDay? 2147483648 = none
#guard Date32.ofCivil? (Date32.toCivil Int32.minValue) = some Int32.minValue
#guard Date32.ofCivil? (Date32.toCivil Int32.maxValue) = some Int32.maxValue

#guard Date64.toCivil? (-86400000) = some ⟨1969, 12, 31⟩
#guard Date64.ofCivil? ⟨2000, 2, 29⟩ = some 951782400000
#guard Date64.ofCivil? ⟨1900, 2, 29⟩ = none
#guard Date64.toCivil? (-1) = none
#guard Date64.toCivil? 1 = none
#guard Date64.toEpochDay? (-86400001) = none
#guard Date64.toEpochDay? 86400001 = none
#guard Date64.toEpochDay? Int64.minValue = none
#guard Date64.toEpochDay? Int64.maxValue = none
#guard Date64.ofEpochDay? (-106751991167) = some (-9223372036828800000)
#guard Date64.ofEpochDay? 106751991167 = some 9223372036828800000
#guard Date64.ofEpochDay? (-106751991168) = none
#guard Date64.ofEpochDay? 106751991168 = none
#guard (Date64.toCivil? (-9223372036828800000)).bind Date64.ofCivil? = some (-9223372036828800000)
#guard (Date64.toCivil? 9223372036828800000).bind Date64.ofCivil? = some 9223372036828800000

#guard ParquetDate.toCivil (-1) = ⟨1969, 12, 31⟩
#guard ParquetDate.ofCivil? ⟨2000, 2, 29⟩ = some 11016
#guard ParquetDate.ofCivil? (ParquetDate.toCivil Int32.minValue) = some Int32.minValue
#guard ParquetDate.ofCivil? (ParquetDate.toCivil Int32.maxValue) = some Int32.maxValue
#guard ParquetDate.ofEpochDay? 2147483648 = none
