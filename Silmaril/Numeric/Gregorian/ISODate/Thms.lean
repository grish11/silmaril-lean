module

public import Silmaril.Numeric.Gregorian.ISODate.Defs
import Silmaril.Numeric.Gregorian.Thms
import Silmaril.Proofs.Numeric.Gregorian.ISODate.Ordinal
import Silmaril.Proofs.Numeric.Gregorian.ISODate.Week

public section

namespace Silmaril.Numeric.Gregorian

theorem weeksInYear_eq (year : Int) : weeksInYear year = 52 ∨ weeksInYear year = 53 :=
  Proofs.Numeric.Gregorian.ISODate.weeksInYear_eq year

namespace OrdinalDate

@[simp] theorem toEpochDay_ofEpochDay (day : Int) : (ofEpochDay day).toEpochDay? = some day :=
  Proofs.Numeric.Gregorian.ISODate.ordinal_toEpochDay_ofEpochDay day

theorem ofEpochDay_toEpochDay {date : OrdinalDate} {day : Int} (h : date.toEpochDay? = some day) :
    ofEpochDay day = date := Proofs.Numeric.Gregorian.ISODate.ordinal_ofEpochDay_toEpochDay h

theorem toCivil_ofCivil {date : CivilDate} {day : Int} (h : date.toEpochDay? = some day) :
    (ofCivil? date).bind toCivil? = some date := by
  simp [ofCivil?, toCivil?, h, CivilDate.ofEpochDay_toEpochDay? h]

theorem ofCivil_toCivil {date : OrdinalDate} {day : Int} (h : date.toEpochDay? = some day) :
    date.toCivil?.bind ofCivil? = some date := by
  simp [ofCivil?, toCivil?, h, CivilDate.toEpochDay?_ofEpochDay, ofEpochDay_toEpochDay h]

end OrdinalDate

namespace WeekDate

@[simp] theorem toEpochDay_ofEpochDay (day : Int) : (ofEpochDay day).toEpochDay? = some day :=
  Proofs.Numeric.Gregorian.ISODate.week_toEpochDay_ofEpochDay day

theorem ofEpochDay_toEpochDay {date : WeekDate} {day : Int} (h : date.toEpochDay? = some day) :
    ofEpochDay day = date := Proofs.Numeric.Gregorian.ISODate.week_ofEpochDay_toEpochDay h

theorem toCivil_ofCivil {date : CivilDate} {day : Int} (h : date.toEpochDay? = some day) :
    (ofCivil? date).bind toCivil? = some date := by
  simp [ofCivil?, toCivil?, h, CivilDate.ofEpochDay_toEpochDay? h]

theorem ofCivil_toCivil {date : WeekDate} {day : Int} (h : date.toEpochDay? = some day) :
    date.toCivil?.bind ofCivil? = some date := by
  simp [ofCivil?, toCivil?, h, CivilDate.toEpochDay?_ofEpochDay, ofEpochDay_toEpochDay h]

end WeekDate

end Silmaril.Numeric.Gregorian
