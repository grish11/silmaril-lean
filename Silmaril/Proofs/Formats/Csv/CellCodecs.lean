module

public import Silmaril.Formats.Csv.Typed.Codecs.Defs
import Silmaril.Formats.Spki.Thms
import Silmaril.Formats.Utf8.Thms

/-! Proofs for `Silmaril.Formats.Csv.Typed.Codecs.Thms`. -/

public section

namespace Silmaril.Proofs.Formats.Csv.CellCodecs

open Silmaril.Formats.Csv.Typed.Codecs
open Silmaril.Formats.Csv.Typed.Codecs.Internal
open Silmaril.Formats.Csv (Field)
open Silmaril.Formats

private theorem isDecimal_decimal (n : Nat) : Spki.IsDecimal (Spki.decimal n) :=
  Spki.isDecimal_iff.mpr ⟨n, rfl⟩

private theorem decimalSpelling_iff (field : Field) (value : Int32) :
    DecimalSpelling field value.toInt ↔ field = int32Text value := by
  by_cases neg : value.toInt < 0
  · simp only [DecimalSpelling, int32Text, neg, ↓reduceIte]
    constructor
    · rintro ⟨magnitude, rfl, hm, denotation⟩
      obtain ⟨n, rfl⟩ := Spki.isDecimal_iff.mp hm
      rw [Spki.digitsValue_decimal] at denotation
      rw [denotation]
    · rintro rfl
      exact ⟨_, rfl, isDecimal_decimal _, Spki.digitsValue_decimal _⟩
  · simp only [DecimalSpelling, int32Text, neg, ↓reduceIte]
    constructor
    · rintro ⟨hm, denotation⟩
      obtain ⟨n, rfl⟩ := Spki.isDecimal_iff.mp hm
      rw [Spki.digitsValue_decimal] at denotation
      rw [denotation]
    · rintro rfl
      exact ⟨isDecimal_decimal _, Spki.digitsValue_decimal _⟩

private theorem unsignedHead (n : Nat) :
    ∃ first rest, Spki.decimal n = first :: rest ∧ first ≠ 0x2D := by
  rcases isDecimal_decimal n with zero | ⟨d, tail, eq, low, _, _⟩
  · exact ⟨0x30, [], zero, by decide⟩
  · refine ⟨d, tail, eq, fun isMinus => ?_⟩
    subst d
    exact (by decide : ¬ (0x31 : UInt8) ≤ 0x2D) low

private theorem signedValue_int32Text (value : Int32) : signedValue (int32Text value) = value.toInt := by
  unfold int32Text
  by_cases neg : value.toInt < 0
  · rw [ite_eq_left neg]
    have abs := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt neg)
    simp [signedValue, Spki.digitsValue_decimal, abs]
  · rw [ite_eq_right neg]
    obtain ⟨first, rest, eq, notMinus⟩ := unsignedHead value.toInt.natAbs
    rw [eq]
    have ex : signedValue (first :: rest) = Int.ofNat (Spki.digitsValue (first :: rest)) := by
      simp [signedValue, notMinus]
    rw [ex, ← eq, Spki.digitsValue_decimal]
    exact Int.natAbs_of_nonneg (Int.le_of_not_gt neg)

private theorem decimal_length_le (fuel n : Nat) (bound : n < 10 ^ (fuel + 1)) :
    (Spki.decimal n).length ≤ fuel + 1 := by
  induction fuel generalizing n with
  | zero =>
    have h : n < 10 := by simpa using bound
    rw [Spki.decimal, ite_eq_left h]
    simp
  | succ fuel ih =>
    rw [Spki.decimal]
    split
    · simp
    · have smaller : n / 10 < 10 ^ (fuel + 1) := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [Nat.pow_succ] using bound
      have length := ih (n / 10) smaller
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      omega

private theorem magnitude_bound (value : Int32) : value.toInt.natAbs < 10^10 := by
  have low : -2147483648 ≤ value.toInt := value.minValue_le_toInt
  have high : value.toInt ≤ 2147483647 := value.toInt_le
  by_cases neg : value.toInt < 0
  · have := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt neg)
    omega
  · have := Int.natAbs_of_nonneg (Int.le_of_not_gt neg)
    omega

private theorem int32Text_length (value : Int32) : (int32Text value).length ≤ 11 := by
  have limit := decimal_length_le 9 value.toInt.natAbs (magnitude_bound value)
  unfold int32Text
  split <;> simp only [List.length_cons] <;> omega

private theorem parseInt32_eq_text_iff (field : Field) (value : Int32) :
    parseInt32 field = some value ↔ field = int32Text value := by
  constructor
  · unfold parseInt32
    intro h
    split at h
    next =>
      dsimp only at h
      split at h
      next =>
        split at h
        next eq => cases h; exact eq.symm
        next => cases h
      next => cases h
    next => cases h
  · rintro rfl
    simp only [parseInt32, int32Text_length, ↓reduceIte, signedValue_int32Text]
    rw [dite_eq_left ⟨value.minValue_le_toInt, value.toInt_le⟩, Int32.ofIntLE_toInt]
    simp

theorem parseInt32_eq_some_iff (field : Field) (value : Int32) :
    parseInt32 field = some value ↔ DecimalSpelling field value.toInt :=
  (parseInt32_eq_text_iff field value).trans (decimalSpelling_iff field value).symm

theorem int32_parsePrint : int32.ParsePrint := by
  intro value field h
  have eq : int32Text value = field := Option.some.inj h
  exact (parseInt32_eq_text_iff field value).mpr eq.symm

theorem int32_printParse : int32.PrintParse := by
  intro value field h
  exact congrArg some ((parseInt32_eq_text_iff field value).mp h).symm

private theorem digit_textByte (b : UInt8) (low : (0x30 : UInt8) ≤ b) (high : b ≤ 0x39) :
    Silmaril.Formats.Csv.Internal.fieldData b = true := by
  have lower : (0x2D : UInt8) ≤ b := UInt8.le_trans (by decide) low
  have upper : b ≤ (0x7E : UInt8) := UInt8.le_trans high (by decide)
  simp [Silmaril.Formats.Csv.Internal.fieldData, Silmaril.Formats.Csv.Internal.quotedData,
    Silmaril.Formats.Csv.Internal.textData, lower, upper]

private theorem decimal_textBytesOK (n : Nat) : textBytesOK (Spki.decimal n) = true := by
  unfold textBytesOK
  rcases isDecimal_decimal n with h | ⟨d, tail, h, low, high, digits⟩
  · rw [h]
    decide
  · rw [h]
    apply List.all_eq_true.mpr
    intro b mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact digit_textByte b (UInt8.le_trans (by decide) low) high
    · have digit : (0x30 : UInt8) ≤ b ∧ b ≤ 0x39 := by
        simpa [Spki.isDigit] using digits b mem
      exact digit_textByte b digit.1 digit.2

theorem int32_textBytesOK (value : Int32) : textBytesOK (int32Text value) = true := by
  unfold int32Text
  split
  · have ok : Silmaril.Formats.Csv.Internal.fieldData 0x2D = true := by decide
    simp only [textBytesOK, List.all_cons, ok, Bool.true_and]
    exact decimal_textBytesOK _
  · exact decimal_textBytesOK _

private theorem toUTF8_fromUTF8? {bytes : ByteArray} {value : String}
    (h : String.fromUTF8? bytes = some value) : value.toByteArray = bytes := by
  unfold String.fromUTF8? at h
  split at h
  · cases h
    rfl
  · cases h

private theorem fromUTF8?_toUTF8 (value : String) : String.fromUTF8? value.toByteArray = some value := by
  rw [String.fromUTF8?, dite_eq_left value.isValidUTF8]
  congr

theorem utf8_parsePrint : utf8.ParsePrint := by
  intro value field h
  change (if textBytesOK value.toByteArray.data.toList then some value.toByteArray.data.toList else none) = some field at h
  split at h
  next valid =>
    obtain rfl := Option.some.inj h
    have bytes : (⟨value.toByteArray.data.toList.toArray⟩ : ByteArray) = value.toByteArray := by
      apply ByteArray.ext
      simp
    change (if textBytesOK value.toByteArray.data.toList then String.fromUTF8? _ else none) = some value
    rw [ite_eq_left valid, bytes, fromUTF8?_toUTF8]
  next => cases h

theorem utf8_printParse : utf8.PrintParse := by
  intro value field h
  change (if textBytesOK field then String.fromUTF8? ⟨field.toArray⟩ else none) = some value at h
  split at h
  next valid =>
    have eq := congrArg (fun bytes : ByteArray => bytes.data.toList) (toUTF8_fromUTF8? h)
    have text : value.toByteArray.data.toList = field := by simpa using eq
    change (if textBytesOK value.toByteArray.data.toList then some value.toByteArray.data.toList else none) = some field
    rw [text, ite_eq_left valid]
  next => cases h

private theorem ascii_of_textBytesOK {field : Field} (ok : textBytesOK field = true) :
    ∀ b ∈ field, b < 0x80 := by
  intro b mem
  have byte := List.all_eq_true.mp ok b mem
  simp [Silmaril.Formats.Csv.Internal.fieldData, Silmaril.Formats.Csv.Internal.quotedData,
    Silmaril.Formats.Csv.Internal.textData, Silmaril.Formats.Csv.Internal.quote,
    Silmaril.Formats.Csv.Internal.comma, Silmaril.Formats.Csv.Internal.cr,
    Silmaril.Formats.Csv.Internal.lf, UInt8.le_iff_toNat_le, or_assoc] at byte
  rw [UInt8.lt_iff_toNat_lt]
  change b.toNat < 128
  rcases byte with h | h | h | h | h | h | h <;> first | (subst b; decide) | omega

theorem utf8_parse_isSome_iff (field : Field) :
    (utf8.parse field).isSome = true ↔ textBytesOK field = true := by
  change (if textBytesOK field then String.fromUTF8? ⟨field.toArray⟩ else none).isSome = true ↔ _
  by_cases ok : textBytesOK field = true
  · have good : Utf8.IsWellFormed field := by
      rw [← Utf8.encode_ofAscii (ascii_of_textBytesOK ok)]
      exact Utf8.isWellFormed_encode _
    simpa [ok, Utf8.fromUTF8?_isSome_iff] using good
  · simp [ok]

theorem utf8_print_eq_some_iff (value : String) (field : Field) :
    utf8.print value = some field ↔ field = value.toByteArray.data.toList ∧ textBytesOK field = true := by
  change (if textBytesOK value.toByteArray.data.toList then some value.toByteArray.data.toList else none) = some field ↔ _
  constructor
  · intro h
    split at h
    next ok => obtain rfl := Option.some.inj h; exact ⟨rfl, ok⟩
    next => cases h
  · rintro ⟨rfl, ok⟩
    simp [ok]

end Silmaril.Proofs.Formats.Csv.CellCodecs
