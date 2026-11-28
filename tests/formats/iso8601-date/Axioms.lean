module

import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Numeric.Gregorian.ISODate.Thms
import Silmaril.Formats.ISO8601.Date.Thms

open Silmaril.Numeric.Gregorian Silmaril.Formats.ISO8601

#print axioms CivilDate.ofEpochDay_year_eq_iff
#print axioms weeksInYear_eq
#print axioms OrdinalDate.toEpochDay_ofEpochDay
#print axioms OrdinalDate.ofEpochDay_toEpochDay
#print axioms OrdinalDate.toCivil_ofCivil
#print axioms OrdinalDate.ofCivil_toCivil
#print axioms WeekDate.toEpochDay_ofEpochDay
#print axioms WeekDate.ofEpochDay_toEpochDay
#print axioms WeekDate.toCivil_ofCivil
#print axioms WeekDate.ofCivil_toCivil
#print axioms parseOrdinalDate_eq_some_iff
#print axioms parseWeekDate_eq_some_iff
#print axioms renderOrdinalDate_eq_none_iff
#print axioms renderWeekDate_eq_none_iff
