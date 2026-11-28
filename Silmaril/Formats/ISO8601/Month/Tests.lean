module

meta import Silmaril.Formats.ISO8601.Month.Defs

open Silmaril.Formats.ISO8601 Silmaril.Numeric.Gregorian

-- The fixture oracle checks this observation against independent signed bounds.
private meta def observes (year : Int) (month : Nat) (start stop : Int) (text : Option String) :
    Bool :=
  let value : CivilMonth := ⟨year, month⟩
  value.interval? == some ⟨start, stop⟩ &&
    CivilMonth.ofEpochDay (start - 1) != value &&
    CivilMonth.ofEpochDay start == value &&
    CivilMonth.ofEpochDay (stop - 1) == value &&
    CivilMonth.ofEpochDay stop == value.next &&
    value.next.interval?.map (·.start) == some stop &&
    renderMonth? value == text &&
    (match text with
    | some spelling => parseMonth? spelling == some value
    | none => true)

#guard observes 0 2 (-719497) (-719468) (some "0000-02")
#guard observes 1900 2 (-25536) (-25508) (some "1900-02")
#guard observes 1969 12 (-31) 0 (some "1969-12")
#guard observes 1970 1 0 31 (some "1970-01")
#guard observes 2000 2 10988 11017 (some "2000-02")
#guard observes 9999 12 2932866 2932897 (some "9999-12")
#guard observes 10000 1 2932897 2932928 none
#guard ((⟨2024, 0⟩ : CivilMonth).interval?).isNone
#guard ((⟨2024, 13⟩ : CivilMonth).interval?).isNone
#guard (renderMonth? ⟨2024, 0⟩).isNone
#guard (renderMonth? ⟨2024, 13⟩).isNone

#guard ["", "2024", "024-02", "2024-2", "202402", "2024/02", "2024-00", "2024-13",
  "2024-02-01", "2024-02T00:00Z", "2024-02 ", "2024-02\n", " 2024-02",
  "-0001-12", "+2024-02", "10000-01", "２０２４-02", "2024-０２"].all
  fun input => (parseMonth? input).isNone
