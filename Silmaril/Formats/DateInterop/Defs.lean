module

public import Silmaril.Numeric.Gregorian.Defs
public import Silmaril.Numeric.UnixRepresentation.Defs

/-! # Arrow Date32/Date64 and Parquet DATE scalar adapters

The input is an already interpreted signed payload. Date32 and Parquet DATE
count days since 1970-01-01. Date64 counts uniform milliseconds from that same
epoch and admits only exact whole days. These adapters use the astronomical
year convention of the proleptic Gregorian model.
-/

@[expose] public section

namespace Silmaril.Formats.DateInterop

open Silmaril.Numeric.Gregorian (CivilDate)
open Silmaril.Numeric.UnixRepresentation (WordFormat)

namespace Internal

def checked (format : WordFormat) (count : Int) : Option format.Payload :=
  if h : format.InRange count then some (format.ofInt count h) else none

end Internal

namespace Date32

/-- Arrow Date32 stores a signed day count. -/
abbrev Payload := Int32

def toEpochDay (value : Payload) : Int := value.toInt

def ofEpochDay? (day : Int) : Option Payload := Internal.checked .int32 day

def toCivil (value : Payload) : CivilDate := CivilDate.ofEpochDay (toEpochDay value)

def ofCivil? (date : CivilDate) : Option Payload := date.toEpochDay?.bind ofEpochDay?

end Date32

namespace Date64

/-- Arrow Date64 stores signed milliseconds on a uniform day scale. -/
abbrev Payload := Int64

def millisecondsPerDay : Int := 86400000

/-- Check exact divisibility before interpreting the millisecond count as a date. -/
def toEpochDay? (value : Payload) : Option Int :=
  if value.toInt % millisecondsPerDay = 0 then some (value.toInt / millisecondsPerDay) else none

/-- Scale in unbounded integers and check the signed word range before narrowing. -/
def ofEpochDay? (day : Int) : Option Payload :=
  Internal.checked .int64 (day * millisecondsPerDay)

def toCivil? (value : Payload) : Option CivilDate := (toEpochDay? value).map CivilDate.ofEpochDay

def ofCivil? (date : CivilDate) : Option Payload := date.toEpochDay?.bind ofEpochDay?

end Date64

namespace ParquetDate

/-- Parquet DATE annotates a signed INT32 count of epoch days. -/
abbrev Payload := Int32

abbrev toEpochDay := Date32.toEpochDay
abbrev ofEpochDay? := Date32.ofEpochDay?
abbrev toCivil := Date32.toCivil
abbrev ofCivil? := Date32.ofCivil?

end ParquetDate

end Silmaril.Formats.DateInterop
