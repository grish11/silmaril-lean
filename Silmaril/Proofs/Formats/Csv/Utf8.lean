module

public import Silmaril.Formats.Csv.Utf8.Defs
import Silmaril.Formats.Csv.Thms
import Silmaril.Formats.Utf8.Thms
import Silmaril.Proofs.Formats.Csv.Codec

/-! Proofs for `Silmaril.Formats.Csv.Utf8.Thms`. -/

public section

namespace Silmaril.Proofs.Formats.Csv.Utf8

open Silmaril.Formats.Csv (Bytes Field Row Rows)
open Silmaril.Formats.Csv.Internal
open Silmaril.Formats.Csv.Utf8
open Silmaril.Formats.Csv.Utf8.Internal (scan)

private abbrev Ascii (bytes : Bytes) : Prop := ∀ b ∈ bytes, b < 0x80

private theorem ascii_tail {b : UInt8} {bs : Bytes} (h : Ascii (b :: bs)) : Ascii bs :=
  fun c mem => h c (List.mem_cons_of_mem _ mem)

private theorem bareData_eq_ascii {b : UInt8} (h : b < 0x80) :
    bareData .utf8Bytes b = textData b := by
  have low : ¬ (0x80 : UInt8) ≤ b := by
    rw [UInt8.le_iff_toNat_le]
    exact Nat.not_le_of_gt (UInt8.lt_iff_toNat_lt.mp h)
  simp [bareData, low]

private theorem quotedData_eq_ascii {b : UInt8} (h : b < 0x80) :
    quotedDataFor .utf8Bytes b = quotedData b := by
  simp [quotedDataFor, quotedData, bareData_eq_ascii h]

private theorem fieldData_eq_ascii {b : UInt8} (h : b < 0x80) :
    fieldDataFor .utf8Bytes b = fieldData b := by
  simp [fieldDataFor, fieldData, quotedData_eq_ascii h]

private theorem readQuoted_ascii (input : Bytes) (ascii : Ascii input) :
    readQuoted input .utf8Bytes = readQuoted input := by
  induction len : input.length using Nat.strongRecOn generalizing input with
  | ind n ih =>
    cases input with
    | nil => rfl
    | cons b bs =>
      rw [readQuoted.eq_def (b :: bs) .utf8Bytes, readQuoted.eq_def (b :: bs) .ascii]
      by_cases start : b = quote
      · cases bs with
        | nil => simp [start]
        | cons c cs =>
          have smaller : cs.length < n := by simp at len; omega
          have tail := ih cs.length smaller cs (ascii_tail (ascii_tail ascii)) rfl
          simp [start, tail]
      · have smaller : bs.length < n := by simp at len; omega
        have tail := ih bs.length smaller bs (ascii_tail ascii) rfl
        simp [start, quotedData_eq_ascii (ascii b List.mem_cons_self), tail]
        rfl

private theorem takeDrop_ascii (input : Bytes) (ascii : Ascii input) :
    input.takeWhile (bareData .utf8Bytes) = input.takeWhile textData ∧
      input.dropWhile (bareData .utf8Bytes) = input.dropWhile textData := by
  induction input with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨take, drop⟩ := ih (ascii_tail ascii)
    simp [List.takeWhile_cons, List.dropWhile_cons, bareData_eq_ascii (ascii b List.mem_cons_self),
      take, drop]

private theorem readField_ascii (input : Bytes) (ascii : Ascii input) :
    readField input .utf8Bytes = readField input := by
  cases input with
  | nil => rfl
  | cons b bs =>
    rw [readField.eq_def (b :: bs) .utf8Bytes, readField.eq_def (b :: bs) .ascii]
    by_cases start : b = quote
    · simp [start, readQuoted_ascii bs (ascii_tail ascii)]
    · obtain ⟨take, drop⟩ := takeDrop_ascii (b :: bs) ascii
      simp only [ite_eq_right start, bareData_ascii]
      congr

private theorem cr_ne_comma : cr ≠ comma := by decide

private theorem readRecords_ascii (input : Bytes) (ascii : Ascii input) :
    readRecords input .utf8Bytes = readRecords input := by
  induction len : input.length using Nat.strongRecOn generalizing input with
  | ind n ih =>
    rw [readRecords.eq_def input .utf8Bytes, readRecords.eq_def input .ascii, readField_ascii input ascii]
    cases hf : readField input with
    | none => rfl
    | some p =>
      obtain ⟨wire, _, shaped⟩ := Silmaril.Proofs.Formats.Csv.readField_sound hf
      have suffix : Ascii p.rest := fun b mem => ascii b (by rw [shaped]; exact List.mem_append_right _ mem)
      rcases p with ⟨field, rest, bound⟩
      cases rest with
      | nil => rfl
      | cons b bs =>
        change (b :: bs).length ≤ input.length at bound
        by_cases separator : b = comma
        · have smaller : bs.length < n := by simp at bound; omega
          have tail := ih bs.length smaller bs (ascii_tail suffix) rfl
          simp [separator, tail]
        · by_cases line : b = cr
          · cases bs with
            | nil => simp [line, cr_ne_comma]
            | cons c rest =>
              cases rest with
              | nil => simp [line, cr_ne_comma]
              | cons d ds =>
                have smaller : (d :: ds).length < n := by simp at bound ⊢; omega
                have tail := ih _ smaller (d :: ds) (ascii_tail (ascii_tail suffix)) rfl
                simp [line, cr_ne_comma, tail]
          · simp [separator, line]

private theorem scan_ascii (wire : Bytes) (ascii : Ascii wire) :
    scan wire = Silmaril.Formats.Csv.decode wire := by
  cases wire with
  | nil => rfl
  | cons b bs => simp [scan, Silmaril.Formats.Csv.decode, readRecords_ascii (b :: bs) ascii]

private theorem rowsOK_iff (rows : Rows) : rowsOK rows = true ↔
    ∀ row ∈ rows, row ≠ [] ∧ ∀ field ∈ row, fieldOK field = true := by
  simp [rowsOK, Bool.and_eq_true]

private theorem fieldOK_ascii {field : Field} (ascii : Ascii field) :
    fieldOK field = true ↔ field.all fieldData = true := by
  have valid : ByteArray.validateUTF8 ⟨field.toArray⟩ = true :=
    Silmaril.Formats.Utf8.validateUTF8_iff.mpr (by simpa using Silmaril.Formats.Utf8.isWellFormed_of_ascii ascii)
  simp only [fieldOK, valid, Bool.and_true, List.all_eq_true]
  constructor <;> intro ok b mem
  · simpa only [fieldData_eq_ascii (ascii b mem)] using ok b mem
  · simpa only [fieldData_eq_ascii (ascii b mem)] using ok b mem

private theorem strictField_ascii {field : Field} (ok : field.all fieldData = true) : Ascii field := by
  intro b mem
  have byte := List.all_eq_true.mp ok b mem
  simp [fieldData, quotedData, textData, quote, comma, cr, lf, UInt8.le_iff_toNat_le, or_assoc] at byte
  rw [UInt8.lt_iff_toNat_lt]
  change b.toNat < 128
  rcases byte with h | h | h | h | h | h | h <;> first | (subst b; decide) | omega

private theorem rowsOK_of_strict {rows : Rows} (h : Silmaril.Formats.Csv.WellFormed rows) :
    rowsOK rows = true := by
  apply (rowsOK_iff rows).mpr
  intro row mem
  refine ⟨(h row mem).1, ?_⟩
  intro field inRow
  have valid := (h row mem).2 field inRow
  exact (fieldOK_ascii (strictField_ascii valid)).mpr valid

theorem decode_eq_ascii (wire : Bytes) (ascii : ∀ b ∈ wire, b < 0x80) :
    decode wire = Silmaril.Formats.Csv.decode wire := by
  unfold decode
  rw [scan_ascii wire ascii]
  cases result : Silmaril.Formats.Csv.decode wire with
  | none => rfl
  | some rows =>
    have source := (Silmaril.Formats.Csv.decode_eq_some_iff _ _).mp result
    have ok := rowsOK_of_strict (Silmaril.Formats.Csv.parses_wellFormed source)
    simp [ok]

theorem encode_eq_ascii (rows : Rows)
    (ascii : ∀ row ∈ rows, ∀ field ∈ row, ∀ b ∈ field, b < 0x80) :
    encode rows = Silmaril.Formats.Csv.encode rows := by
  unfold encode Silmaril.Formats.Csv.encode
  have same : rowsOK rows = rows.all (fun row => !row.isEmpty && row.all (·.all fieldData)) := by
    apply Bool.eq_iff_iff.mpr
    rw [rowsOK_iff]
    simp only [List.all_eq_true, Bool.and_eq_true]
    constructor
    · intro ok row mem
      exact ⟨by simpa using (ok row mem).1, fun field inRow =>
        List.all_eq_true.mp ((fieldOK_ascii (ascii row mem field inRow)).mp ((ok row mem).2 field inRow))⟩
    · intro ok row mem
      exact ⟨by simpa using (ok row mem).1, fun field inRow =>
        (fieldOK_ascii (ascii row mem field inRow)).mpr (List.all_eq_true.mpr ((ok row mem).2 field inRow))⟩
  rw [same]

private theorem readPrintedField (field tail : Bytes) (ok : fieldOK field = true)
    (boundary : tail.head? ≠ some quote) :
    ∃ p, readField (quoteField field ++ tail) .utf8Bytes = some p ∧ p.field = field ∧ p.rest = tail := by
  have alphabet : field.all (fieldDataFor .utf8Bytes) = true := by
    simp only [fieldOK, Bool.and_eq_true] at ok
    exact ok.1
  obtain ⟨p, hp, hf, ht⟩ := Silmaril.Proofs.Formats.Csv.readQuoted_complete .utf8Bytes field tail
    alphabet boundary
  have shaped : quoteField field ++ tail = quote :: (escape field ++ quote :: tail) := by
    simp [quoteField, List.append_assoc]
  rw [shaped]
  refine ⟨⟨p.field, p.rest, by have := p.rest_le; simp at *; omega⟩, ?_, hf, ht⟩
  simp [readField, hp]

private theorem readRecords_renderRow {row : Row} {tail : Bytes} {later : Rows}
    (ok : row ≠ [] ∧ ∀ field ∈ row, fieldOK field = true) (next : scan tail = some later) :
    readRecords (renderRow row ++ tail) .utf8Bytes = some (row, later) := by
  induction row with
  | nil => exact (ok.1 rfl).elim
  | cons field fields ih =>
    have good : fieldOK field = true := ok.2 field List.mem_cons_self
    cases fields with
    | nil =>
      have boundary : (cr :: lf :: tail).head? ≠ some quote := by simp only [List.head?_cons]; decide
      obtain ⟨⟨value, rest, _⟩, hp, hf, hr⟩ := readPrintedField field (cr :: lf :: tail) good boundary
      change value = field at hf
      change rest = cr :: lf :: tail at hr
      subst value rest
      have shaped : renderRow [field] ++ tail = quoteField field ++ cr :: lf :: tail := by
        simp [renderRow, List.append_assoc]
      rw [shaped, readRecords.eq_def, hp]
      cases tail with
      | nil =>
        have eq : later = [] := (Option.some.inj next).symm
        subst later
        simp [cr_ne_comma]
      | cons b bs =>
        cases readTail : readRecords (b :: bs) .utf8Bytes with
        | none => simp [scan, readTail] at next
        | some pair =>
          obtain ⟨row, rest⟩ := pair
          have eq : row :: rest = later := by simpa [scan, readTail] using next
          subst later
          simp [cr_ne_comma, readTail]
    | cons f fs =>
      have all : f :: fs ≠ [] ∧ ∀ cell ∈ f :: fs, fieldOK cell = true :=
        ⟨by simp, fun cell mem => ok.2 cell (List.mem_cons_of_mem _ mem)⟩
      have boundary : (comma :: (renderRow (f :: fs) ++ tail)).head? ≠ some quote := by
        simp only [List.head?_cons]; decide
      obtain ⟨⟨value, rest, _⟩, hp, hf, hr⟩ :=
        readPrintedField field (comma :: (renderRow (f :: fs) ++ tail)) good boundary
      change value = field at hf
      change rest = comma :: (renderRow (f :: fs) ++ tail) at hr
      subst value rest
      have shaped : renderRow (field :: f :: fs) ++ tail =
          quoteField field ++ comma :: (renderRow (f :: fs) ++ tail) := by
        simp [renderRow, List.append_assoc]
      rw [shaped, readRecords.eq_def, hp]
      simp [ih all]

private theorem scan_render (rows : Rows) (ok : rowsOK rows = true) : scan (render rows) = some rows := by
  induction rows with
  | nil => simp only [render, List.flatMap_nil, scan]
  | cons row rows ih =>
    have all := (rowsOK_iff _).mp ok
    have hrow := all row List.mem_cons_self
    have hrows := (rowsOK_iff _).mpr fun item mem => all item (List.mem_cons_of_mem _ mem)
    have scanned := readRecords_renderRow hrow (ih hrows)
    have nonempty : renderRow row ++ render rows ≠ [] := by
      simp [Silmaril.Proofs.Formats.Csv.renderRow_ne_nil hrow.1]
    rw [render, List.flatMap_cons]
    change scan (renderRow row ++ render rows) = _
    cases form : renderRow row ++ render rows with
    | nil => exact (nonempty form).elim
    | cons b bs => simp [scan, form ▸ scanned]

theorem decode_encode {rows : Rows} {wire : Bytes} (h : encode rows = some wire) : decode wire = some rows := by
  unfold encode at h
  split at h
  next ok =>
    have eq : render rows = wire := Option.some.inj h
    subst wire
    simp [decode, scan_render rows ok, ok]
  next => cases h

theorem decode_fields_utf8 {wire : Bytes} {rows : Rows} (h : decode wire = some rows) :
    ∀ row ∈ rows, ∀ field ∈ row, (⟨field.toArray⟩ : ByteArray).IsValidUTF8 := by
  unfold decode at h
  cases scanned : scan wire with
  | none => simp [scanned] at h
  | some result =>
    rw [scanned] at h
    change (if rowsOK result then some result else none) = some rows at h
    split at h
    next ok =>
      cases h
      intro row mem field inRow
      have fieldGood := ((rowsOK_iff _).mp ok row mem).2 field inRow
      simp only [fieldOK, Bool.and_eq_true] at fieldGood
      exact ByteArray.validateUTF8_eq_true_iff.mp fieldGood.2
    next => cases h

end Silmaril.Proofs.Formats.Csv.Utf8
