module

public import Silmaril.Formats.Parquet.PlainV1Writer.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.Payload.Uncompressed.Thms
import Silmaril.Prelude.Bytes.Digits.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.PlainV1Writer

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.PlainV1Writer

private theorem singleton_wire (slot : Option Int32) :
    (Hybrid.Run.repeated 1 (if slot.isSome then 1 else 0)).wire 1 =
      [2, if slot.isSome then 1 else 0] := by
  cases slot <;> simp [Hybrid.Run.wire, Hybrid.uleb, Hybrid.repeatedByteCount] <;> rfl

private theorem definition_length (slots : List (Option Int32)) :
    (definitionOctets slots).length = 2 * slots.length := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    simp [definitionOctets, singleton_wire] at ih ⊢
    omega

private theorem definition_wire (slots : List (Option Int32)) :
    Hybrid.Wire 1 slots.length (definitionOctets slots) (slots.map (fun slot => if slot.isSome then 1 else 0)) := by
  induction slots with
  | nil => exact .empty
  | cons slot rest ih =>
    let run := Hybrid.Run.repeated 1 (if slot.isSome then 1 else 0)
    have valid : run.Valid 1 := by
      cases slot <;> simp [run, Hybrid.Run.Valid, Hybrid.Run.size, Hybrid.runLimit]
    have fits : run.Fits (slot :: rest).length := by simp [run, Hybrid.Run.Fits]
    have next := Hybrid.Wire.next (run := run) (remaining := (slot :: rest).length)
      (by simp) valid fits (show Hybrid.Wire 1 ((slot :: rest).length - run.size) _ _ from ih)
    simpa [run, Hybrid.Run.values, definitionOctets, List.take] using next

private theorem encode_length (values : List Int32) : (Plain.encodeInt32 values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [Plain.encodeInt32, Plain.encodeWords, Plain.writeUInt32Word, KBytes.length_unpack] at ih ⊢
    omega

theorem body_length (input : Input) : input.body.length = input.bodySize := by
  cases input with
  | required values => exact encode_length values
  | optional slots =>
    simp [Input.body, Input.bodySize, KBytes.length_unpack, definition_length, encode_length,
      List.length_filterMap_eq_countP]

private theorem split_optional (slots : List (Option Int32)) (limits : Limits)
    (fits : (Input.optional slots).Fits limits) :
    FlatPage.split .optional limits.scalar.levels.bytes (.v1 (Input.optional slots).body) =
      .ok ⟨Bytes.ofList (definitionOctets slots), Plain.encodeInt32 (slots.filterMap id)⟩ := by
  change FlatPage.splitV1Optional _ _ = _
  apply FlatPage.splitV1Optional_ok_iff.mpr
  refine ⟨KBytes.unpack 4 (definitionOctets slots).length, KBytes.length_unpack _ _, ?_, ?_, ?_⟩
  · rw [Bytes.length_ofList, KBytes.leVal_unpack, Nat.mod_eq_of_lt]
    rw [definition_length]
    have size := fits.2.2.2.1
    change 4 + 2 * slots.length + 4 * slots.countP Option.isSome < 2 ^ 31 at size
    omega
  · simpa [definition_length, Input.definitionSize] using fits.2.2.1
  · simp [Input.body, List.append_assoc]

private theorem mask_optional (slots : List (Option Int32)) (limits : Limits)
    (fits : (Input.optional slots).Fits limits) :
    FlatPage.readMask .optional slots.length limits.scalar.levels (Bytes.ofList (definitionOctets slots)) =
      .ok (slots.map Option.isSome) := by
  apply FlatPage.readMask_ok_iff.mpr
  refine ⟨fits.1, fits.2.1, ?_, ?_⟩
  · simpa [definition_length, Input.definitionSize] using fits.2.2.1
  · refine ⟨_, by simpa using definition_wire slots, ?_⟩
    rw [List.map_map]
    apply congrArg (fun f => slots.map f)
    funext slot
    cases slot <;> rfl

private theorem mask_required (values : List Int32) (limits : Limits)
    (fits : (Input.required values).Fits limits) :
    FlatPage.readMask .required values.length limits.scalar.levels .empty = .ok (List.replicate values.length true) :=
  FlatPage.readMask_ok_iff.mpr ⟨fits.1, fits.2.1, by simp, rfl, rfl⟩

private theorem payload_body (input : Input) (limits : Limits) (fits : input.Fits limits) :
    Payload.decode (limits.scalar.payloadBounds input.parameters.sizes 0)
      input.parameters.codec input.body.toList = .ok input.body.toList := by
  obtain ⟨_, _, _, _, compressed, uncompressed⟩ := fits
  apply Payload.decode_uncompressed
  · simpa [ScalarPage.Limits.payloadBounds, Input.parameters] using compressed
  · simpa [ScalarPage.Limits.payloadBounds, Input.parameters] using uncompressed
  · simp [ScalarPage.Limits.payloadBounds, Input.parameters, body_length]
  · simp [ScalarPage.Limits.payloadBounds, Input.parameters, body_length]

private theorem validate_body (input : Input) (limits : Limits) (fits : input.Fits limits) :
    ScalarPage.validate input.parameters limits.scalar input.body =
      .ok (match input with | .required _ => FlatPage.Layout.required | .optional _ => .optional) := by
  obtain ⟨count, slotLimit, _, size, compressed, uncompressed⟩ := fits
  simp only [ScalarPage.validate, ScalarPage.validateFor, Input.parameters,
    ne_eq, not_true_eq_false, ite_false, or_self, body_length]
  simp only [Nat.not_le.mpr size, Nat.not_lt.mpr compressed, Nat.not_lt.mpr uncompressed,
    Nat.not_le.mpr count, Nat.not_lt.mpr slotLimit, false_or, ite_false]
  cases input <;> rfl

private theorem prepare_body (input : Input) (limits : Limits) (fits : input.Fits limits) :
    ScalarPage.prepare input.parameters limits.scalar input.body =
      .ok ⟨input.slots.map Option.isSome, Plain.encodeInt32 (input.slots.filterMap id)⟩ := by
  have valid := validate_body input limits fits
  have stored := payload_body input limits fits
  unfold ScalarPage.prepare ScalarPage.prepareFor
  rw [show ScalarPage.validateFor 0 input.parameters limits.scalar input.body = _ from valid]
  change ScalarPage.prepareV1 input.parameters limits.scalar _ 3 3 input.body = _
  simp only [ScalarPage.prepareV1, ne_eq, not_true_eq_false, or_self, ite_false]
  rw [show Payload.decode (limits.scalar.payloadBounds input.parameters.sizes 0) input.parameters.codec
    input.body.toList = _ from stored]
  simp only [Except.mapError, Bind.bind, Except.bind, Bytes.ofList_toList]
  cases input with
  | required values =>
    simp [FlatPage.split, Input.body, Input.parameters, Input.numValues, mask_required values limits fits,
      Input.slots, List.map_map, List.filterMap_map, Function.comp_def, List.map_const', Pure.pure, Except.pure]
  | optional slots =>
    simp [split_optional slots limits fits, mask_optional slots limits fits, Input.slots,
      Input.parameters, Input.numValues, Pure.pure, Except.pure]

theorem decode_body {input : Input} {limits : Limits} (fits : input.Fits limits) :
    ScalarPage.decode .int32 input.parameters limits.scalar input.body = .ok input.slots := by
  have plain : Plain.decodeInt32 ((input.slots.map Option.isSome).count true)
      (Plain.encodeInt32 (input.slots.filterMap id)) = .ok (input.slots.filterMap id) := by
    simpa [List.count_eq_countP, List.countP_map, Function.comp_def, List.length_filterMap_eq_countP] using
      Plain.decodeInt32_encodeInt32 (input.slots.filterMap id)
  have reconstructed : FlatPage.reconstruct (input.slots.map Option.isSome) (input.slots.filterMap id) =
      .ok input.slots := FlatPage.reconstruct_ok_iff.mpr ⟨rfl, rfl⟩
  simp [ScalarPage.decode, prepare_body input limits fits, ScalarPage.Kind.readPlain, plain,
    reconstructed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.PlainV1Writer
