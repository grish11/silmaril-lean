module

import Silmaril.Formats.ISO8601.Date.Defs
meta import Silmaril.Formats.ISO8601.Date.Defs
meta import Silmaril.Numeric.Gregorian.Defs
meta import Silmaril.Numeric.Gregorian.ISODate.Defs

open Silmaril.Formats.ISO8601
open Silmaril.Numeric.Gregorian

-- Ordinal day 366 is present only in a Gregorian leap year.
#guard parseOrdinalDate? "1900-366" = none
#guard parseOrdinalDate? "2000-366" = some ⟨2000, 366⟩
#guard parseOrdinalDate? "0000-366" = some ⟨0, 366⟩
#guard (parseOrdinalDate? "1969-365").bind OrdinalDate.toEpochDay? = some (-1)
#guard (OrdinalDate.ofEpochDay (-719529)).toCivil? = some ⟨-1, 12, 31⟩
#guard renderOrdinalDate? ⟨-1, 365⟩ = none
#guard renderOrdinalDate? ⟨10000, 1⟩ = none
#guard renderOrdinalDate? ⟨2000, 1⟩ = some "2000-001"
#guard parseOrdinalDate? "2000-000" = none
#guard parseOrdinalDate? "2000-01" = none
#guard parseOrdinalDate? "2000001" = none
#guard parseOrdinalDate? "2000-00１" = none
#guard parseOrdinalDate? "2000-001T00:00:00Z" = none

-- Week-year boundaries use the Monday of the week containing January 4.
#guard (parseWeekDate? "2020-W53-7").bind WeekDate.toCivil? = some ⟨2021, 1, 3⟩
#guard WeekDate.ofCivil? ⟨2018, 12, 31⟩ = some ⟨2019, 1, 1⟩
#guard WeekDate.ofEpochDay 0 = ⟨1970, 1, 4⟩
#guard (parseWeekDate? "1970-W01-1").bind WeekDate.toEpochDay? = some (-3)
#guard (WeekDate.ofEpochDay (-719529)).toCivil? = some ⟨-1, 12, 31⟩
#guard parseWeekDate? "2021-W53-1" = none
#guard parseWeekDate? "2020-W53-0" = none
#guard parseWeekDate? "2020-W53-8" = none
#guard parseWeekDate? "2020-W00-1" = none
#guard parseWeekDate? "2020-w53-1" = none
#guard parseWeekDate? "2020-W3-1" = none
#guard parseWeekDate? "2020-W53-1 " = none
#guard renderWeekDate? ⟨0, 1, 1⟩ = some "0000-W01-1"
#guard renderWeekDate? ⟨10000, 1, 1⟩ = none
