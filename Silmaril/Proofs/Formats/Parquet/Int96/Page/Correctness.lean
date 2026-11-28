module

public import Silmaril.Formats.Parquet.Int96.Page.Defs
import Silmaril.Formats.Parquet.Int96.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Page

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Page

theorem parameters_sound {leaf : Footer.SchemaElement} {codec : Int} {header : Page.Header}
    {params : ScalarPage.Parameters} (checked : parameters leaf codec header = .ok params) :
    leafLevels? leaf = some params.schema ∧ codec = 0 ∧ params.codec = codec ∧ header.crc = none ∧
      params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ ∧
      match header.kind with
      | .dataV1 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v1 info.definitionLevelEncoding info.repetitionLevelEncoding
      | .dataV2 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
            (some info.isCompressed)
      | _ => False := by
  cases levels : leafLevels? leaf with
  | none => simp [parameters, levels] at checked
  | some schema =>
    by_cases uncompressed : codec = 0
    · cases checksum : header.crc <;> cases kind : header.kind <;>
        simp_all [parameters, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> subst params <;> simp
    · simp [parameters, levels, uncompressed, Bind.bind, Except.bind] at checked

private theorem slot_eq_ok_iff (index : Nat) (word : Option Bytes) (payload : Option Int96.Payload) :
    decodeSlot index word = .ok payload ↔ word.map Bytes.toList = payload.map Int96.Payload.encode := by
  cases word with
  | none => cases payload <;> simp [decodeSlot]
  | some word =>
    cases payload with
    | none =>
      cases read : Int96.Payload.decode? word.toList <;> simp [decodeSlot, read]
    | some payload =>
      constructor
      · intro checked
        have read : Int96.Payload.decode? word.toList = some payload := by
          cases read : Int96.Payload.decode? word.toList <;>
            simp_all [decodeSlot]
        simpa using (Int96.Payload.encode_of_decode read).symm
      · intro exactBytes
        simp only [Option.map_some, Option.some.injEq] at exactBytes
        simp [decodeSlot, exactBytes, Int96.Payload.decode_encode]

private theorem decodeSlots_cons (start : Nat) (head : Option Bytes) (tail : List (Option Bytes)) :
    decodeSlots start (head :: tail) = (do
      let first ← decodeSlot start head
      let rest ← decodeSlots (start + 1) tail
      pure (first :: rest)) := by
  simp only [decodeSlots, List.zipIdx_cons, List.mapM_cons]

private theorem cons_ok_iff {E A : Type*} (head : Except E A) (tail : Except E (List A))
    (output : List A) :
    (do let first ← head; let rest ← tail; pure (first :: rest)) = .ok output ↔
      ∃ first rest, head = .ok first ∧ tail = .ok rest ∧ first :: rest = output := by
  cases head <;> cases tail <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem decodeSlots_eq_ok_iff (start : Nat) (raw : List (Option Bytes))
    (payloads : List (Option Int96.Payload)) :
    decodeSlots start raw = .ok payloads ↔
      raw.map (Option.map Bytes.toList) = payloads.map (Option.map Int96.Payload.encode) := by
  induction raw generalizing start payloads with
  | nil => cases payloads <;> simp [decodeSlots, Pure.pure, Except.pure]
  | cons first tail ih =>
    rw [decodeSlots_cons, cons_ok_iff]
    cases payloads <;> simp [slot_eq_ok_iff, ih]

private theorem slot_eq_invalidWord_iff (start index : Nat) (word : Option Bytes) :
    decodeSlot start word = .error (.invalidWord index) ↔
      ∃ bad, word = some bad ∧ Int96.Payload.decode? bad.toList = none ∧ index = start := by
  cases word with
  | none => simp [decodeSlot]
  | some word =>
    cases read : Int96.Payload.decode? word.toList <;>
      simp [decodeSlot, read, eq_comm]

theorem decodeSlots_eq_invalidWord_iff (start : Nat) (raw : List (Option Bytes)) (index : Nat) :
    decodeSlots start raw = .error (.invalidWord index) ↔
      ∃ before bad after, raw = before ++ some bad :: after ∧
        (∃ payloads, decodeSlots start before = .ok payloads) ∧
        Int96.Payload.decode? bad.toList = none ∧ index = start + before.length := by
  constructor
  · induction raw generalizing start with
    | nil => simp [decodeSlots, Pure.pure, Except.pure]
    | cons first tail ih =>
      intro checked
      cases one : decodeSlot start first with
      | error cause =>
        have same : cause = .invalidWord index := by
          simpa [decodeSlots_cons, one, Bind.bind, Except.bind] using checked
        obtain ⟨bad, rfl, failed, position⟩ :=
          (slot_eq_invalidWord_iff start index first).mp (one.trans (congrArg Except.error same))
        exact ⟨[], bad, tail, rfl, ⟨[], rfl⟩, failed, by simpa using position⟩
      | ok payload =>
        have remaining : decodeSlots (start + 1) tail = .error (.invalidWord index) := by
          cases rest : decodeSlots (start + 1) tail <;>
            simp_all [decodeSlots_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]
        obtain ⟨before, bad, after, rfl, ⟨previous, valid⟩, invalid, position⟩ := ih _ remaining
        refine ⟨first :: before, bad, after, rfl, ⟨payload :: previous, ?_⟩, invalid, ?_⟩
        · simp [decodeSlots_cons, one, valid, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · simpa [Nat.add_assoc, Nat.add_comm 1] using position
  · rintro ⟨before, bad, after, rfl, ⟨payloads, prefixOk⟩, badWord, rfl⟩
    have failed := (slot_eq_invalidWord_iff (start + before.length) (start + before.length) (some bad)).mpr
      ⟨bad, rfl, badWord, rfl⟩
    unfold decodeSlots at prefixOk ⊢
    simp [List.zipIdx_append, List.mapM_cons, prefixOk, failed, Bind.bind, Except.bind]

theorem decode_eq_ok_iff {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))} :
    decode policy leaf codec header limits body = .ok output ↔
      ∃ params raw, ∃ payloads : List (Option Int96.Payload), parameters leaf codec header = .ok params ∧
        ScalarPage.decode (.fixedLenBytes 12) params limits body = .ok raw ∧
        raw.map (Option.map Bytes.toList) = payloads.map (Option.map Int96.Payload.encode) ∧
        output = payloads.map (Option.map (·.toTicks policy)) := by
  cases checked : parameters leaf codec header with
  | error cause => simp [decode, checked, Bind.bind, Except.bind]
  | ok params =>
    cases physical : ScalarPage.decode (.fixedLenBytes 12) params limits body with
    | error cause => simp [decode, checked, physical, Bind.bind, Except.bind, Except.mapError]
    | ok raw =>
      have logical :
          decode policy leaf codec header limits body = .ok output ↔
            ∃ payloads, decodeSlots 0 raw = .ok payloads ∧
              output = payloads.map (Option.map (·.toTicks policy)) := by
        cases parsed : decodeSlots 0 raw <;>
          simp [decode, checked, physical, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure, parsed, eq_comm]
      rw [logical]
      constructor
      · rintro ⟨payloads, parsed, mapped⟩
        exact ⟨params, raw, payloads, rfl, physical, (decodeSlots_eq_ok_iff _ _ _).mp parsed, mapped⟩
      · rintro ⟨otherParams, otherRaw, payloads, sameParams, sameRaw, ordered, mapped⟩
        cases Except.ok.inj sameParams
        cases Except.ok.inj (physical.symm.trans sameRaw)
        exact ⟨payloads, (decodeSlots_eq_ok_iff _ _ _).mpr ordered, mapped⟩

theorem decode_eq_invalidWord_iff {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {index : Nat} :
    decode policy leaf codec header limits body = .error (.invalidWord index) ↔
      ∃ params before bad after, parameters leaf codec header = .ok params ∧
        ScalarPage.decode (.fixedLenBytes 12) params limits body = .ok (before ++ some bad :: after) ∧
        (∃ payloads, decodeSlots 0 before = .ok payloads) ∧
        Int96.Payload.decode? bad.toList = none ∧ index = before.length := by
  cases checked : parameters leaf codec header with
  | error cause =>
    have rejected : cause ≠ .invalidWord index := by
      intro same
      subst cause
      cases levels : leafLevels? leaf <;>
        by_cases codecOk : codec = 0 <;> cases checksum : header.crc <;> cases kind : header.kind <;>
        simp [parameters, levels, codecOk, checksum, kind, Bind.bind, Except.bind, Pure.pure, Except.pure] at checked
    simp [decode, checked, Bind.bind, Except.bind, rejected]
  | ok params =>
    cases physical : ScalarPage.decode (.fixedLenBytes 12) params limits body with
    | error cause => simp [decode, checked, physical, Bind.bind, Except.bind, Except.mapError]
    | ok raw =>
      have first :
          decode policy leaf codec header limits body = .error (.invalidWord index) ↔
            decodeSlots 0 raw = .error (.invalidWord index) := by
        cases parsed : decodeSlots 0 raw <;>
          simp [decode, checked, physical, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure, parsed]
      rw [first, decodeSlots_eq_invalidWord_iff]
      simp [physical]


private theorem exactUncompressed {compressed expected : Nat} {input output : List UInt8}
    (wire : ScalarPage.ExactPayload compressed expected 0 input output) :
    input = output ∧ input.length = compressed ∧ output.length = expected := by
  obtain ⟨compressedSize, expectedSize, codec, selected, decoded⟩ := wire
  have same : Parquet.Payload.Codec.uncompressed = codec := Option.some.inj selected
  subst codec
  cases decoded
  exact ⟨rfl, compressedSize, expectedSize⟩

private theorem prepared_extents {params : ScalarPage.Parameters} {limits : ScalarPage.Limits}
    {layout : FlatPage.Layout} {body : Bytes} {prepared : ScalarPage.Prepared}
    (codec : params.codec = 0) (wire : ScalarPage.PreparedWire params limits layout body prepared) :
    body.length = params.sizes.compressed ∧ body.length = params.sizes.uncompressed := by
  cases version : params.version with
  | v1 definitionEncoding repetitionEncoding =>
    rw [ScalarPage.PreparedWire, version] at wire
    obtain ⟨_, _, expanded, _, exactPayload, _⟩ := wire
    rw [codec] at exactPayload
    obtain ⟨same, packedSize, expandedSize⟩ := exactUncompressed exactPayload
    rw [← same] at expandedSize
    simpa using And.intro packedSize expandedSize
  | v2 nulls rows repetitionBytes definitionBytes flag =>
    rw [ScalarPage.PreparedWire, version] at wire
    obtain ⟨_, _, _, packedBound, expandedBound, _, definitions, encoded,
      definitionSize, splitBody, _, _, exactPayload⟩ := wire
    have effective : ScalarPage.v2Codec params.codec flag = 0 := by
      simp [ScalarPage.v2Codec, codec, Parquet.Payload.Codec.id]
    rw [effective] at exactPayload
    obtain ⟨same, packedSize, expandedSize⟩ := exactUncompressed exactPayload
    rw [← same] at expandedSize
    have bodySize : body.length = definitionBytes + encoded.length := by
      simpa [definitionSize] using congrArg List.length splitBody
    omega

private theorem present_eq_of_slots {raw : List (Option Bytes)}
    {payloads : List (Option Int96.Payload)}
    (ordered : raw.map (Option.map Bytes.toList) = payloads.map (Option.map Int96.Payload.encode)) :
    (raw.filterMap id).map Bytes.toList = (payloads.filterMap id).map Int96.Payload.encode := by
  simpa [List.filterMap_map, List.map_filterMap, Function.comp_def] using
    congrArg (List.filterMap id) ordered

private theorem mask_eq_of_slots {α β γ : Type} {raw : List (Option α)} {slots : List (Option β)}
    {f : α → γ} {g : β → γ}
    (ordered : raw.map (Option.map f) = slots.map (Option.map g)) :
    raw.map Option.isSome = slots.map Option.isSome := by
  simpa [List.map_map, Function.comp_def] using congrArg (List.map Option.isSome) ordered

theorem decode_wire_sound {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))}
    (decoded : decode policy leaf codec header limits body = .ok output) :
    body.length = header.compressedSize ∧ body.length = header.uncompressedSize ∧
      ∃ params layout prepared, ∃ payloads : List (Option Int96.Payload),
        parameters leaf codec header = .ok params ∧
        ScalarPage.validate params limits body = .ok layout ∧
        ScalarPage.PreparedWire params limits layout body prepared ∧
        output.map Option.isSome = prepared.mask ∧
        prepared.scalars.toList = (payloads.filterMap id).flatMap Int96.Payload.encode ∧
        prepared.scalars.length = prepared.mask.count true * 12 ∧
        output = payloads.map (Option.map (·.toTicks policy)) := by
  obtain ⟨params, raw, payloads, selected, physical, ordered, mapped⟩ :=
    decode_eq_ok_iff.mp decoded
  obtain ⟨prepared, words, preparedOk, wordsOk, mask, present, _, bytes⟩ :=
    ScalarPage.decode_sound physical
  obtain ⟨layout, validated, wire⟩ := ScalarPage.prepare_sound preparedOk
  obtain ⟨_, codecId, paramsCodec, _, sizes, _⟩ := parameters_sound selected
  have extents := prepared_extents (paramsCodec.trans codecId) wire
  rw [sizes] at extents
  refine ⟨extents.1, extents.2, params, layout, prepared, payloads, selected, validated, wire,
    ?_, ?_, bytes, mapped⟩
  · rw [mapped, ← mask]
    simpa [List.map_map, Function.comp_def] using (mask_eq_of_slots ordered).symm
  · have fixed : Plain.decodeFixedWidth 12 (prepared.mask.count true) Bytes.ofList prepared.scalars
        = .ok words := by
      change Plain.decodeFixedLenBytes 12 (prepared.mask.count true) prepared.scalars = .ok words at wordsOk
      simpa only [Plain.decodeFixedLenBytes, ite_eq_left (by decide : 12 < (2 : Nat) ^ 31)] using wordsOk
    obtain ⟨_, chunks, exact, _, _, read⟩ := Plain.decodeFixedWidth_ok_iff.mp fixed
    have bytesEq := present_eq_of_slots ordered
    rw [present, read] at bytesEq
    simp only [List.map_map, Function.comp_def, Bytes.toList_ofList, List.map_id'] at bytesEq
    rw [exact, bytesEq, List.flatMap_def]

theorem decode_counts {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))}
    (decoded : decode policy leaf codec header limits body = .ok output) :
    match header.kind with
    | .dataV1 info => output.length = info.numValues
    | .dataV2 info => output.length = info.numValues ∧
        (output.filterMap id).length = info.numValues - info.numNulls
    | _ => False := by
  obtain ⟨params, raw, payloads, selected, physical, ordered, rfl⟩ := decode_eq_ok_iff.mp decoded
  have slots : raw.length = payloads.length := by simpa using congrArg List.length ordered
  have present : (raw.filterMap id).length = (payloads.filterMap id).length := by
    simpa using congrArg List.length (present_eq_of_slots ordered)
  have ⟨count, byVersion⟩ := ScalarPage.decode_counts physical
  have fields := (parameters_sound selected).2.2.2.2.2
  cases kind : header.kind <;> rw [kind] at fields
  case dataV1 info =>
    obtain ⟨values, _, _⟩ := fields
    simpa [← slots] using count.trans values
  case dataV2 info =>
    obtain ⟨values, _, version⟩ := fields
    rw [version] at byVersion
    refine ⟨by simpa [← slots] using count.trans values, ?_⟩
    have mapped :
        (payloads.map (Option.map (·.toTicks policy))).filterMap id =
          (payloads.filterMap id).map (·.toTicks policy) := by
      simp only [List.filterMap_map, List.map_filterMap, Function.comp_def, id_eq]
    rw [mapped, List.length_map, ← present, ← values]
    exact byVersion
  case dictionary => exact fields.elim
  case skipped => exact fields.elim

end Silmaril.Proofs.Formats.Parquet.Int96.Page
