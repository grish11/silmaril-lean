module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Payload.Uncompressed.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Prelude.Bytes.Digits.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.PlainByteArrayV1Writer

private theorem singleton_wire (present : Bool) :
    (Hybrid.Run.repeated 1 (if present then 1 else 0)).wire 1 = [2, if present then 1 else 0] := by
  cases present <;> simp [Hybrid.Run.wire, Hybrid.uleb, Hybrid.repeatedByteCount] <;> rfl

theorem definition_length (mask : List Bool) : (definitionOctets mask).length = 2 * mask.length := by
  induction mask with
  | nil => rfl
  | cons present rest ih =>
    simp [definitionOctets, singleton_wire] at ih ⊢
    omega

private theorem definition_wire (mask : List Bool) :
    Hybrid.Wire 1 mask.length (definitionOctets mask) (mask.map (fun present => if present then 1 else 0)) := by
  induction mask with
  | nil => exact .empty
  | cons present rest ih =>
    let run := Hybrid.Run.repeated 1 (if present then 1 else 0)
    have valid : run.Valid 1 := by
      cases present <;> simp [run, Hybrid.Run.Valid, Hybrid.Run.size, Hybrid.runLimit]
    have fits : run.Fits (present :: rest).length := by simp [run, Hybrid.Run.Fits]
    have next := Hybrid.Wire.next (run := run) (remaining := (present :: rest).length)
      (by simp) valid fits (show Hybrid.Wire 1 ((present :: rest).length - run.size) _ _ from ih)
    simpa [run, Hybrid.Run.values, definitionOctets, List.take] using next

theorem body_length (input : Input) {scalars : Bytes} (size : scalars.length = Plain.ByteArray.encodedSize input.values) :
    (input.body scalars).length = input.bodySize := by
  cases input <;> simp [Input.body, Input.bodySize, Input.definitionSize, KBytes.length_unpack, definition_length, size]

private theorem split_optional (slots : List (Option Bytes)) (limits : Limits) (scalars : Bytes)
    (fits : (Input.optional slots).Fits limits) :
    FlatPage.split .optional limits.page.scalar.levels.bytes (.v1 ((Input.optional slots).body scalars)) =
      .ok ⟨Bytes.ofList (definitionOctets (slots.map Option.isSome)), scalars⟩ := by
  change FlatPage.splitV1Optional _ _ = _
  apply FlatPage.splitV1Optional_ok_iff.mpr
  refine ⟨KBytes.unpack 4 (definitionOctets (slots.map Option.isSome)).length,
    KBytes.length_unpack _ _, ?_, ?_, ?_⟩
  · rw [Bytes.length_ofList, KBytes.leVal_unpack, Nat.mod_eq_of_lt]
    rw [definition_length, List.length_map]
    have size := fits.2.2.2.1
    change 4 + 2 * slots.length + Plain.ByteArray.encodedSize (slots.filterMap id) < 2 ^ 31 at size
    omega
  · simpa [definition_length, Input.definitionSize] using fits.2.2.1
  · simp [Input.body, List.append_assoc]

private theorem mask_optional (slots : List (Option Bytes)) (limits : Limits)
    (fits : (Input.optional slots).Fits limits) :
    FlatPage.readMask .optional slots.length limits.page.scalar.levels
      (Bytes.ofList (definitionOctets (slots.map Option.isSome))) = .ok (slots.map Option.isSome) := by
  apply FlatPage.readMask_ok_iff.mpr
  refine ⟨fits.1, fits.2.1, ?_, ?_⟩
  · simpa [definition_length, Input.definitionSize] using fits.2.2.1
  · refine ⟨_, by simpa using definition_wire (slots.map Option.isSome), ?_⟩
    rw [List.map_map]
    apply congrArg (fun f => slots.map f)
    funext slot
    cases slot <;> rfl

private theorem mask_required (values : List Bytes) (limits : Limits)
    (fits : (Input.required values).Fits limits) :
    FlatPage.readMask .required values.length limits.page.scalar.levels .empty =
      .ok (List.replicate values.length true) :=
  FlatPage.readMask_ok_iff.mpr ⟨fits.1, fits.2.1, by simp, rfl, rfl⟩

theorem prepare_body {input : Input} {limits : Limits} {scalars : Bytes} (fits : input.Fits limits)
    (size : scalars.length = Plain.ByteArray.encodedSize input.values) :
    ScalarPage.prepare input.parameters limits.page.scalar (input.body scalars) =
      .ok ⟨input.slots.map Option.isSome, scalars⟩ := by
  have length := body_length input size
  have stored : Payload.decode (limits.page.scalar.payloadBounds input.parameters.sizes 0)
      input.parameters.codec (input.body scalars).toList = .ok (input.body scalars).toList := by
    apply Payload.decode_uncompressed
    · simpa [ScalarPage.Limits.payloadBounds, Input.parameters] using fits.2.2.2.2.1
    · simpa [ScalarPage.Limits.payloadBounds, Input.parameters] using fits.2.2.2.2.2
    · simp [ScalarPage.Limits.payloadBounds, Input.parameters, length]
    · simp [ScalarPage.Limits.payloadBounds, Input.parameters, length]
  have valid : ScalarPage.validateFor 0 input.parameters limits.page.scalar (input.body scalars) =
      .ok (match input with | .required _ => FlatPage.Layout.required | .optional _ => .optional) := by
    obtain ⟨count, slotLimit, _, signed, compressed, uncompressed⟩ := fits
    simp only [ScalarPage.validateFor, Input.parameters, ne_eq, not_true_eq_false, ite_false, or_self, length]
    simp only [Nat.not_le.mpr signed, Nat.not_lt.mpr compressed, Nat.not_lt.mpr uncompressed,
      Nat.not_le.mpr count, Nat.not_lt.mpr slotLimit, false_or, ite_false]
    cases input <;> rfl
  unfold ScalarPage.prepare ScalarPage.prepareFor
  rw [valid]
  change ScalarPage.prepareV1 input.parameters limits.page.scalar _ 3 3 (input.body scalars) = _
  simp only [ScalarPage.prepareV1, ne_eq, not_true_eq_false, or_self, ite_false]
  rw [show Payload.decode (limits.page.scalar.payloadBounds input.parameters.sizes 0) input.parameters.codec
    (input.body scalars).toList = _ from stored]
  simp only [Except.mapError, Bind.bind, Except.bind, Bytes.ofList_toList]
  cases input with
  | required values =>
    simp [FlatPage.split, Input.body, Input.parameters, Input.numValues, mask_required values limits fits,
      Input.slots, List.map_map, Function.comp_def, List.map_const', Pure.pure, Except.pure]
  | optional slots =>
    simp [split_optional slots limits scalars fits, mask_optional slots limits fits, Input.slots,
      Input.parameters, Input.numValues, Pure.pure, Except.pure]

theorem emit_exact {limits : Limits} {input : Input} {page : Encoded} (written : emit limits input = .ok page) :
    input.Fits limits ∧ page.headerBytes.length ≤ limits.page.headerBytes ∧
      PlainV1Writer.encodeHeader input.numValues input.bodySize = some page.headerBytes ∧
      page.header = input.header ∧
      Page.readHeaderPrefix limits.page.header page.wire = .ok (page.header, page.headerBytes.length) ∧
      page.header.compressedSize = page.body.length ∧ page.header.uncompressedSize = page.body.length ∧
      page.wire.length = page.headerBytes.length + page.body.length ∧
      ∃ scalars, Plain.ByteArray.encode limits.plain input.values = .ok scalars ∧ page.body = input.body scalars := by
  by_cases fits : input.Fits limits
  · cases encoded : PlainV1Writer.encodeHeader input.numValues input.bodySize with
    | none => simp [emit, fits, encoded] at written
    | some headerBytes =>
      by_cases bounded : headerBytes.length ≤ limits.page.headerBytes
      · cases plain : Plain.ByteArray.encode limits.plain input.values with
        | error cause => simp [emit, fits, encoded, Nat.not_lt.mpr bounded, plain] at written
        | ok scalars =>
          let candidate : Encoded := ⟨input.header, headerBytes, input.body scalars⟩
          simp only [emit, fits, ite_true, encoded, Nat.not_lt.mpr bounded, ite_false, plain] at written
          change (match Page.readHeaderPrefix limits.page.header candidate.wire with
            | .error cause => Except.error (Error.header cause)
            | .ok parsed => if parsed = (candidate.header, headerBytes.length) then Except.ok candidate
                else Except.error Error.headerMismatch) = Except.ok page at written
          cases checked : Page.readHeaderPrefix limits.page.header candidate.wire with
          | error cause => simp [checked] at written
          | ok parsed =>
            rw [checked] at written
            change (if parsed = (candidate.header, headerBytes.length) then Except.ok candidate
              else Except.error Error.headerMismatch) = Except.ok page at written
            by_cases equal : parsed = (candidate.header, headerBytes.length)
            · simp only [equal, ite_true] at written
              have same := Except.ok.inj written
              subst page
              have length := body_length input (Plain.ByteArray.encode_size plain)
              exact ⟨fits, bounded, rfl, rfl, checked.trans (congrArg Except.ok equal),
                length.symm, length.symm, Bytes.length_append _ _, scalars, rfl, rfl⟩
            · simp [equal] at written
      · simp [emit, fits, encoded, Nat.lt_of_not_ge bounded] at written
  · simp [emit, fits] at written

theorem emit_prepared {limits : Limits} {input : Input} {page : Encoded} (written : emit limits input = .ok page) :
    ∃ scalars, Plain.ByteArray.encode limits.plain input.values = .ok scalars ∧
      ScalarPage.prepare input.parameters limits.page.scalar page.body =
        .ok ⟨input.slots.map Option.isSome, scalars⟩ := by
  obtain ⟨fits, _, _, _, _, _, _, _, scalars, encoded, body⟩ := emit_exact written
  exact ⟨scalars, encoded, body ▸ prepare_body fits (Plain.ByteArray.encode_size encoded)⟩

theorem emit_roundTrip {limits : Limits} {input : Input} {page : Encoded}
    (written : emit limits input = .ok page) :
    ScalarPage.decode (.byteArray limits.plain) input.parameters limits.page.scalar page.body = .ok input.slots := by
  obtain ⟨scalars, encoded, prepared⟩ := emit_prepared written
  have slots : input.slots.filterMap id = input.values := by
    cases input <;> simp [Input.slots, Input.values, List.filterMap_map, Function.comp_def]
  have count : (input.slots.map Option.isSome).count true = input.values.length := by
    rw [← slots, List.length_filterMap_eq_countP, List.count_eq_countP, List.countP_map]
    rfl
  have rebuilt : FlatPage.reconstruct (input.slots.map Option.isSome) input.values = .ok input.slots :=
    FlatPage.reconstruct_ok_iff.mpr ⟨rfl, slots⟩
  simp [ScalarPage.decode, prepared, ScalarPage.Kind.readPlain, count, Plain.ByteArray.decode_encode encoded,
    rebuilt, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer
