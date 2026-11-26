module

public import Silmaril.Formats.Csv.Typed.Utf8.Defs
import Silmaril.Formats.Csv.Typed.Thms
import Silmaril.Formats.Csv.Utf8.Thms

/-! Proofs for `Silmaril.Formats.Csv.Typed.Utf8.Thms`. -/

public section

namespace Silmaril.Proofs.Formats.Csv.TypedUtf8

open Silmaril.Formats.Csv (Bytes Rows)
open Silmaril.Formats.Csv.Typed (Schema Table CellCodec exportRows importRows)
open Silmaril.Formats.Csv.Typed.Utf8

theorem string_parsePrint : string.ParsePrint := by
  intro value field h
  have eq : value.toByteArray.data.toList = field := Option.some.inj h
  have bytes : (⟨field.toArray⟩ : ByteArray) = value.toByteArray := by
    apply ByteArray.ext
    simp [← eq]
  change String.fromUTF8? ⟨field.toArray⟩ = some value
  rw [bytes, String.fromUTF8?, dite_eq_left value.isValidUTF8]
  congr

theorem string_printParse : string.PrintParse := by
  intro value field h
  change String.fromUTF8? ⟨field.toArray⟩ = some value at h
  unfold String.fromUTF8? at h
  split at h
  · cases h
    change some field.toArray.toList = some field
    simp
  · cases h

variable {Kind : Type*} {Value : Kind → Type*} {schema : Schema Kind}
variable {codecs : (kind : Kind) → CellCodec (Value kind)}

theorem decode_encode (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {wire : Bytes} (h : encode schema codecs table = .ok wire) :
    decode schema codecs wire = .ok table := by
  cases emitted : exportRows schema codecs table with
  | error e => simp [encode, emitted] at h
  | ok rows =>
    cases rendered : Silmaril.Formats.Csv.Utf8.encode rows with
    | none => simp [encode, emitted, rendered] at h
    | some bytes =>
      have eq : bytes = wire := by simpa [encode, emitted, rendered] using h
      subst wire
      simp [decode, Silmaril.Formats.Csv.Utf8.decode_encode rendered,
        Silmaril.Formats.Csv.Typed.importRows_exportRows law emitted]

theorem encode_of_decode (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {input : Bytes} (h : decode schema codecs input = .ok table) :
    ∃ output, encode schema codecs table = .ok output ∧
      Silmaril.Formats.Csv.Utf8.decode output = Silmaril.Formats.Csv.Utf8.decode input := by
  cases scanned : Silmaril.Formats.Csv.Utf8.decode input with
  | none => simp [decode, scanned] at h
  | some rows =>
    have parsed : importRows schema codecs rows = .ok table := by simpa [decode, scanned] using h
    have emitted := Silmaril.Formats.Csv.Typed.exportRows_importRows law parsed
    cases rendered : Silmaril.Formats.Csv.Utf8.encode rows with
    | none =>
      simp [Silmaril.Formats.Csv.Utf8.encode,
        Silmaril.Formats.Csv.Utf8.decode_rowsOK scanned] at rendered
    | some output =>
      exact ⟨output, by simp [encode, emitted, rendered],
        Silmaril.Formats.Csv.Utf8.decode_encode rendered⟩

theorem encode_eq_ascii (table : Table schema Value)
    (ascii : ∀ rows, exportRows schema codecs table = .ok rows →
      ∀ row ∈ rows, ∀ field ∈ row, ∀ b ∈ field, b < 0x80) :
    encode schema codecs table = Silmaril.Formats.Csv.Typed.encode schema codecs table := by
  cases emitted : exportRows schema codecs table with
  | error e => rw [encode, Silmaril.Formats.Csv.Typed.encode, emitted]; rfl
  | ok rows =>
    simp [encode, Silmaril.Formats.Csv.Typed.encode, emitted,
      Silmaril.Formats.Csv.Utf8.encode_eq_ascii rows (ascii rows emitted)]
    rfl

end Silmaril.Proofs.Formats.Csv.TypedUtf8
