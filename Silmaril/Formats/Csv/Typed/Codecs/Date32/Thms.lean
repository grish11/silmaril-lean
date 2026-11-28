module

public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Defs
import Silmaril.Proofs.Formats.Csv.Date32

/-! # Exact Date32 calendar cells and typed CSV round trips -/

public section

namespace Silmaril.Formats.Csv.Typed.Codecs.Date32

/-- These are the inclusive signed epoch days for 0000-01-01 through 9999-12-31. -/
theorem admitted_iff_signed (value : Payload) :
    Admitted value ↔ -719528 ≤ value.toInt ∧ value.toInt ≤ 2932896 :=
  Proofs.Formats.Csv.Date32.admitted_iff_signed value

/-- Printing succeeds exactly at the canonical spelling of an admitted day. -/
theorem print_eq_some_iff (value : Payload) (field : Field) :
    print value = some field ↔
      Admitted value ∧ field = Internal.calendarText (DateInterop.Date32.toCivil value) :=
  Proofs.Formats.Csv.Date32.print_eq_some_iff value field

theorem print_eq_none_iff (value : Payload) : print value = none ↔ ¬ Admitted value := by
  unfold print
  split <;> simp_all

/-- Accepted field bytes are exactly those produced by the encoder for that same Date32 word. -/
theorem parse_eq_some_iff (field : Field) (value : Payload) :
    parse field = some value ↔ print value = some field :=
  Proofs.Formats.Csv.Date32.parse_eq_some_iff field value

/-- Every accepted field consumes exactly ten bytes. -/
theorem parse_length {field : Field} {value : Payload} (accepted : parse field = some value) :
    field.length = 10 :=
  Proofs.Formats.Csv.Date32.parse_length accepted

theorem codec_parsePrint : codec.ParsePrint := fun printed =>
  (parse_eq_some_iff _ _).mpr printed

theorem codec_printParse : codec.PrintParse := fun parsed =>
  (parse_eq_some_iff _ _).mp parsed

variable {Kind : Type*} {schema : Schema Kind} {nullable : Kind → Bool}

/-- The required-field check passes exactly when every null is in a nullable column. -/
theorem firstRequiredNull_eq_none_iff (table : Table schema Cell) :
    firstRequiredNull schema nullable table = none ↔
      ∀ row ∈ table, ∀ column,
        nullable (schema.kind column).2 = true ∨ (row column).isSome = true :=
  Proofs.Formats.Csv.Date32.firstRequiredNull_eq_none_iff schema nullable table

theorem encode_requiredNull {table : Table schema Cell} {row column : Nat}
    (missing : firstRequiredNull schema nullable table = some (row, column)) :
    encode schema nullable table = .error (.requiredNull row column) := by
  simp [encode, missing]

theorem decode_requiredNull {wire : Bytes} {table : Table schema Cell} {row column : Nat}
    (parsed : Utf8.decode schema (fun _ => codec) wire = .ok table)
    (missing : firstRequiredNull schema nullable table = some (row, column)) :
    decode schema nullable wire = .error (.requiredNull row column) := by
  simp [decode, parsed, missing, Except.mapError, Bind.bind, Except.bind]

/-- Export outside the date profile yields the typed print error at the present cell. -/
theorem exportCell_outside (value : Payload) (column : Nat) (outside : ¬ Admitted value) :
    Typed.Internal.exportCell codec column (some value) = .error (.printCell column) := by
  simp [Typed.Internal.exportCell, codec, (print_eq_none_iff value).mpr outside]

/-- A present cell outside the accepted date language yields the typed parse error. -/
theorem importCell_unaccepted (field : Field) (column : Nat) (bad : parse field = none) :
    Typed.Internal.importCell codec column (Typed.Internal.textTag :: field) =
      .error (.parseCell column) := by
  simp [Typed.Internal.importCell, Typed.Internal.textTag, Typed.Internal.nullTag, codec, bad]

/-- Successful wire export preserves ordered rows, null slots and exact Date32 words. -/
theorem decode_encode {table : Table schema Cell} {wire : Bytes}
    (written : encode schema nullable table = .ok wire) :
    decode schema nullable wire = .ok table :=
  Proofs.Formats.Csv.Date32.decode_encode schema nullable written

/-- Re-encoding an admitted wire import preserves its exact lexical rows. -/
theorem encode_of_decode {input : Bytes} {table : Table schema Cell}
    (read : decode schema nullable input = .ok table) :
    ∃ output, encode schema nullable table = .ok output ∧
      Csv.Utf8.decode output = Csv.Utf8.decode input :=
  Proofs.Formats.Csv.Date32.encode_of_decode schema nullable read

end Silmaril.Formats.Csv.Typed.Codecs.Date32
