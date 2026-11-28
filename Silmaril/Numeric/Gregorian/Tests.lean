module

import Silmaril.Numeric.Gregorian.Thms
meta import Silmaril.Numeric.Gregorian.Defs

/-! Executable controls for dates on either side of the epoch and Gregorian boundaries. -/

open Silmaril.Numeric.Gregorian
open CivilDate (ofEpochDay)

-- The Unix epoch, its previous day, and the whole-day Parquet example.
#guard (⟨1970, 1, 1⟩ : CivilDate).toEpochDay? = some 0
#guard ofEpochDay 0 = ⟨1970, 1, 1⟩
#guard (⟨1969, 12, 31⟩ : CivilDate).toEpochDay? = some (-1)
#guard ofEpochDay (-1) = ⟨1969, 12, 31⟩
#guard ofEpochDay 2 = ⟨1970, 1, 3⟩

-- Common, leap, common-century and leap-century years.
#guard (⟨2023, 2, 29⟩ : CivilDate).toEpochDay? = none
#guard (⟨2024, 2, 29⟩ : CivilDate).valid
#guard (⟨1900, 2, 29⟩ : CivilDate).toEpochDay? = none
#guard ofEpochDay (-25509) = ⟨1900, 2, 28⟩
#guard ofEpochDay (-25508) = ⟨1900, 3, 1⟩
#guard (⟨2000, 2, 29⟩ : CivilDate).toEpochDay? = some 11016
#guard ofEpochDay 11016 = ⟨2000, 2, 29⟩
#guard ofEpochDay 11017 = ⟨2000, 3, 1⟩
#guard (⟨2100, 2, 29⟩ : CivilDate).toEpochDay? = none

-- Astronomical numbering, including era boundaries and BCE century rules.
#guard ofEpochDay (-719529) = ⟨-1, 12, 31⟩
#guard ofEpochDay (-719528) = ⟨0, 1, 1⟩
#guard (⟨0, 2, 29⟩ : CivilDate).toEpochDay? = some (-719469)
#guard ofEpochDay (-719469) = ⟨0, 2, 29⟩
#guard ofEpochDay (-719163) = ⟨0, 12, 31⟩
#guard ofEpochDay (-719162) = ⟨1, 1, 1⟩
#guard (⟨-100, 2, 29⟩ : CivilDate).toEpochDay? = none
#guard ofEpochDay (-865566) = ⟨-400, 2, 29⟩

-- Proleptic Gregorian numbering is continuous across October 1582.
#guard ofEpochDay (-141438) = ⟨1582, 10, 4⟩
#guard ofEpochDay (-141437) = ⟨1582, 10, 5⟩

-- Month and day bounds and a short month outside February.
#guard (⟨1970, 0, 1⟩ : CivilDate).toEpochDay? = none
#guard (⟨1970, 13, 1⟩ : CivilDate).toEpochDay? = none
#guard (⟨1970, 1, 0⟩ : CivilDate).toEpochDay? = none
#guard (⟨1970, 4, 31⟩ : CivilDate).toEpochDay? = none
#guard (⟨1970, 4, 30⟩ : CivilDate).valid
#guard (⟨1970, 1, 31⟩ : CivilDate).valid

-- Large offsets also use the same unbounded arithmetic.
#guard (ofEpochDay (-9223372036854775808)).toEpochDay? = some (-9223372036854775808)
#guard (ofEpochDay 9223372036854775807).toEpochDay? = some 9223372036854775807

example (day : Int) : (ofEpochDay day).valid = true :=
  (CivilDate.valid_iff _).mpr (CivilDate.ofEpochDay_valid day)
