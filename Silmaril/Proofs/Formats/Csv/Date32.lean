module

public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Defs
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.DateInterop.Thms
import Silmaril.Numeric.Gregorian.Thms
import Mathlib.Order.Monotone.Basic

public section

namespace Silmaril.Proofs.Formats.Csv.Date32

open Silmaril.Formats
open Silmaril.Formats.Csv
open Silmaril.Formats.Csv.Typed
open Silmaril.Formats.Csv.Typed.Codecs.Date32
open Silmaril.Numeric.Gregorian

private theorem digits_length (width value : Nat) :
    (Internal.digits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [Internal.digits, ih]

private theorem readDigits_digits (width value : Nat) (bounded : value < 10 ^ width) :
    Internal.readDigits (Internal.digits width value) = some value := by
  induction width generalizing value with
  | zero =>
    simp at bounded
    have zero : value = 0 := by omega
    simp [Internal.digits, Internal.readDigits, zero]
  | succ width ih =>
    have power : 0 < 10 ^ width := Nat.pow_pos (by decide)
    have small : value / 10 ^ width < 10 := by
      apply (Nat.div_lt_iff_lt_mul power).2
      simpa [Nat.pow_succ, Nat.mul_comm] using bounded
    have digitBound : 48 + value / 10 ^ width < 256 :=
      lt_trans (Nat.add_lt_add_left small 48) (by decide)
    have leading : (UInt8.ofNat (48 + value / 10 ^ width)).toNat =
        48 + value / 10 ^ width := UInt8.toNat_ofNat_of_lt' digitBound
    have digitRange : 48 ≤ 48 + value / 10 ^ width ∧ 48 + value / 10 ^ width ≤ 57 :=
      ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.le_of_lt_succ small) _⟩
    have tail := ih (value % 10 ^ width) (Nat.mod_lt _ power)
    simp only [Internal.digits, Internal.readDigits, leading, digitRange,
      digits_length, tail, Bind.bind, Option.bind, pure, Pure.pure]
    rw [Nat.add_sub_cancel_left, Nat.mul_comm, Nat.add_comm]
    exact congrArg some (Nat.mod_add_div value (10 ^ width))

private theorem calendarText_length (date : CivilDate) : (Internal.calendarText date).length = 10 := by
  simp [Internal.calendarText, digits_length]

private theorem candidate_calendarText (date : CivilDate) (year : 0 ≤ date.year ∧ date.year < 10000)
    (valid : date.Valid) : Internal.candidate (Internal.calendarText date) = some date := by
  rcases date with ⟨y, m, d⟩
  have yearDigits : y.toNat < 10 ^ 4 := by
    change 0 ≤ y ∧ y < 10000 at year
    change y.toNat < 10000
    omega
  have monthDigits : m < 10 ^ 2 := by
    change m < 100
    exact lt_of_le_of_lt valid.2.1 (by decide)
  have dayDigits : d < 10 ^ 2 := by
    have maxDays : daysInMonth y m ≤ 31 := by
      rw [daysInMonth_eq]
      repeat' first | omega | split
    change d < 100
    exact lt_of_le_of_lt (valid.2.2.2.trans maxDays) (by decide)
  have yearValue : (y.toNat : Int) = y := Int.toNat_of_nonneg year.1
  simp [Internal.candidate, digits_length, Internal.calendarText, List.append_assoc,
    readDigits_digits _ _ yearDigits,
    readDigits_digits _ _ monthDigits, readDigits_digits _ _ dayDigits,
    Bind.bind, Option.bind, pure, Pure.pure, yearValue]

theorem print_eq_some_iff (value : Payload) (field : Field) :
    print value = some field ↔
      Admitted value ∧ field = Internal.calendarText (DateInterop.Date32.toCivil value) := by
  by_cases admitted : Admitted value <;> simp [print, admitted, eq_comm]

theorem parse_eq_some_iff (field : Field) (value : Payload) :
    parse field = some value ↔ print value = some field := by
  constructor
  · intro accepted
    cases observed : Internal.candidate field with
    | none => simp [parse, observed, Bind.bind, Option.bind] at accepted
    | some date =>
      cases converted : DateInterop.Date32.ofCivil? date with
      | none => simp [parse, observed, converted, Bind.bind, Option.bind] at accepted
      | some word =>
        by_cases canonical : print word = some field
        · have eq : word = value := by
            simpa [parse, observed, converted, canonical, Bind.bind, Option.bind] using accepted
          simpa [eq] using canonical
        · simp [parse, observed, converted, canonical, Bind.bind, Option.bind] at accepted
  · intro printed
    obtain ⟨admitted, rfl⟩ := (print_eq_some_iff value field).mp printed
    have valid : (DateInterop.Date32.toCivil value).Valid :=
      CivilDate.ofEpochDay_valid value.toInt
    simp [parse, candidate_calendarText _ admitted valid, DateInterop.Date32.ofCivil?_toCivil,
      printed, Bind.bind, Option.bind]

theorem parse_length {field : Field} {value : Payload} (accepted : parse field = some value) :
    field.length = 10 := by
  obtain ⟨_, rfl⟩ := (print_eq_some_iff value field).mp ((parse_eq_some_iff field value).mp accepted)
  exact calendarText_length _

private theorem yearStart_strictMono : StrictMono yearStart := by
  apply strictMono_int_of_lt_succ
  intro year
  rw [yearStart_succ]
  unfold daysInYear
  split <;> omega

theorem admitted_iff_signed (value : Payload) :
    Admitted value ↔ -719528 ≤ value.toInt ∧ value.toInt ≤ 2932896 := by
  let day := value.toInt
  let year := (CivilDate.ofEpochDay day).year
  change 0 ≤ year ∧ year < 10000 ↔ -719528 ≤ day ∧ day ≤ 2932896
  have bracket := (CivilDate.ofEpochDay_year_eq_iff (day := day) (year := year)).mp rfl
  have first : yearStart 0 = -719528 := by decide
  have stop : yearStart 10000 = 2932897 := by decide
  constructor
  · rintro ⟨low, high⟩
    have before := yearStart_strictMono.monotone low
    have after := yearStart_strictMono.monotone (show year + 1 ≤ 10000 by omega)
    omega
  · rintro ⟨low, high⟩
    constructor
    · by_contra neg
      have before := yearStart_strictMono.monotone (show year + 1 ≤ 0 by omega)
      omega
    · by_contra large
      have after := yearStart_strictMono.monotone (show 10000 ≤ year by omega)
      omega

theorem firstRequiredNull_eq_none_iff {Kind : Type*} (schema : Schema Kind)
    (nullable : Kind → Bool) (table : Table schema Cell) :
    firstRequiredNull schema nullable table = none ↔
      ∀ row ∈ table, ∀ column,
        nullable (schema.kind column).2 = true ∨ (row column).isSome = true := by
  unfold firstRequiredNull
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro clean row belongs column
    obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp belongs
    have checked := clean (row, index) (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
    have noColumn : (List.finRange schema.width).find? (fun column =>
        !(nullable (schema.kind column).2) && (row column).isNone) = none := by
      simpa only [Option.map_eq_none_iff] using checked
    have accepted := List.find?_eq_none.mp noColumn column (by simp)
    cases nullableEq : nullable (schema.kind column).2 <;>
      cases cellEq : row column <;> simp_all
  · intro clean pair belongs
    have rowIn := List.fst_mem_of_mem_zipIdx belongs
    obtain ⟨row, index⟩ := pair
    simp only [Option.map_eq_none_iff]
    apply List.find?_eq_none.mpr
    intro column _
    rcases clean row rowIn column with nullableColumn | present
    · simp [nullableColumn]
    · cases cellEq : row column <;> simp_all

theorem decode_encode {Kind : Type*} (schema : Schema Kind) (nullable : Kind → Bool)
    {table : Table schema Cell} {wire : Bytes} (written : Codecs.Date32.encode schema nullable table = .ok wire) :
    Codecs.Date32.decode schema nullable wire = .ok table := by
  cases missing : firstRequiredNull schema nullable table with
  | some positions =>
    obtain ⟨row, column⟩ := positions
    simp [Codecs.Date32.encode, missing] at written
  | none =>
    cases wireResult : Typed.Utf8.encode schema (fun _ => codec) table with
    | error => simp [Codecs.Date32.encode, missing, wireResult, Except.mapError] at written
    | ok actual =>
      have same : actual = wire := by
        simpa [Codecs.Date32.encode, missing, wireResult, Except.mapError] using written
      subst wire
      have decoded := Typed.Utf8.decode_encode (fun _ => fun printed =>
        (parse_eq_some_iff _ _).mpr printed) wireResult
      simp [Codecs.Date32.decode, decoded, missing, Except.mapError, Bind.bind, Except.bind]

theorem encode_of_decode {Kind : Type*} (schema : Schema Kind) (nullable : Kind → Bool)
    {input : Bytes} {table : Table schema Cell} (read : Codecs.Date32.decode schema nullable input = .ok table) :
    ∃ output, Codecs.Date32.encode schema nullable table = .ok output ∧ Csv.Utf8.decode output = Csv.Utf8.decode input := by
  cases typed : Typed.Utf8.decode schema (fun _ => codec) input with
  | error => simp [Codecs.Date32.decode, typed, Except.mapError, Bind.bind, Except.bind] at read
  | ok actual =>
    cases missing : firstRequiredNull schema nullable actual with
    | some positions =>
      obtain ⟨row, column⟩ := positions
      simp [Codecs.Date32.decode, typed, missing, Except.mapError, Bind.bind, Except.bind] at read
    | none =>
      have same : actual = table := by
        simpa [Codecs.Date32.decode, typed, missing, Except.mapError, Bind.bind, Except.bind] using read
      subst table
      obtain ⟨output, encoded, exactRows⟩ := Typed.Utf8.encode_of_decode
        (fun _ => fun parsed => (parse_eq_some_iff _ _).mp parsed) typed
      exact ⟨output, by simp [Codecs.Date32.encode, missing, encoded, Except.mapError], exactRows⟩

end Silmaril.Proofs.Formats.Csv.Date32
