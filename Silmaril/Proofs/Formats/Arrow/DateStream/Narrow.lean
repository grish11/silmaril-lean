module

public import Silmaril.Formats.Arrow.DateStream.Narrow.Defs
import Silmaril.Formats.Arrow.DateStream.Thms
import Silmaril.Formats.Arrow.DateValues.Thms
import Silmaril.Formats.DateInterop.Thms
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream.Narrow

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateStream
open Silmaril.Formats.Arrow.DateStream.Narrow
open Silmaril.Formats.DateInterop
open Silmaril.Numeric.Gregorian (CivilDate)

private theorem cons_ok_iff {E β : Type*} (head : Except E β) (tail : Except E (List β))
    (output : List β) :
    (do let b ← head; let bs ← tail; pure (b :: bs)) = .ok output ↔
      ∃ b bs, head = .ok b ∧ tail = .ok bs ∧ b :: bs = output := by
  cases head <;> cases tail <;> simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem indexed_ok_iff {E α β : Type*} (f : α × Nat → Except E β) (back : β → α)
    (slotLaw : ∀ item index result, f (item, index) = .ok result ↔ back result = item)
    (items : List α) (start : Nat) (outputs : List β) :
    (items.zipIdx start).mapM f = .ok outputs ↔ outputs.map back = items := by
  induction items generalizing start outputs with
  | nil => cases outputs <;> simp [Pure.pure, Except.pure]
  | cons item tail ih =>
    rw [List.zipIdx_cons, List.mapM_cons, cons_ok_iff]
    cases outputs with
    | nil => simp
    | cons result rest => simp [slotLaw, ih]

private theorem indexed_error_iff {E α β : Type*} (f : α × Nat → Except E β)
    (items : List α) (start : Nat) (error : E) :
    (items.zipIdx start).mapM f = .error error ↔
      ∃ before item after, items = before ++ item :: after ∧
        (∃ outputs, (before.zipIdx start).mapM f = .ok outputs) ∧
        f (item, start + before.length) = .error error := by
  constructor
  · induction items generalizing start with
    | nil => simp [Pure.pure, Except.pure]
    | cons item rest ih =>
      intro failed
      cases first : f (item, start) with
      | error cause =>
        have same : cause = error := by
          simpa [List.mapM_cons, first, Bind.bind, Except.bind] using failed
        subst cause
        exact ⟨[], item, rest, rfl, ⟨[], rfl⟩, by simpa using first⟩
      | ok result =>
        cases remaining : (rest.zipIdx (start + 1)).mapM f with
        | ok outputs =>
          simp [List.mapM_cons, first, remaining, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at failed
        | error cause =>
          have same : cause = error := by
            simpa [List.mapM_cons, first, remaining, Bind.bind, Except.bind] using failed
          subst cause
          obtain ⟨before, bad, after, rfl, ⟨outputs, prefixOk⟩, badSlot⟩ := ih _ remaining
          refine ⟨item :: before, bad, after, rfl, ⟨result :: outputs, ?_⟩, ?_⟩
          · simp [List.mapM_cons, first, prefixOk, Bind.bind, Except.bind, Pure.pure, Except.pure]
          · simpa [Nat.add_assoc, Nat.add_comm 1] using badSlot
  · rintro ⟨before, item, after, rfl, ⟨outputs, prefixOk⟩, badSlot⟩
    simp [List.zipIdx_append, List.mapM_cons, prefixOk, badSlot, Bind.bind, Except.bind]

private theorem slot_ok_iff (batch slot : Nat) (date : Option CivilDate)
    (word : Option Date32.Payload) :
    Internal.narrowSlot batch slot date = .ok word ↔ word.map Date32.toCivil = date := by
  cases date with
  | none => cases word <;> simp [Internal.narrowSlot]
  | some date =>
    cases word with
    | none =>
      cases day : date.toEpochDay? with
      | none => simp [Internal.narrowSlot, day]
      | some count =>
        cases narrowed : Date32.ofEpochDay? count <;>
          simp [Internal.narrowSlot, day, narrowed, Pure.pure, Except.pure]
    | some word =>
      rw [Option.map_some, Option.some.injEq, ← Date32.ofCivil?_eq_some_iff]
      cases day : date.toEpochDay? with
      | none => simp [Internal.narrowSlot, Date32.ofCivil?, day]
      | some count =>
        cases narrowed : Date32.ofEpochDay? count <;>
          simp [Internal.narrowSlot, Date32.ofCivil?, day, narrowed,
            Pure.pure, Except.pure]

private theorem batch_ok_iff (index : Nat) (dates : DateValues.Column) (words : Narrow.Column) :
    Internal.narrowBatch index dates = .ok words ↔
      words.map (Option.map Date32.toCivil) = dates :=
  indexed_ok_iff (fun (date, slot) => Internal.narrowSlot index slot date) _
    (fun date slot => slot_ok_iff index slot date) dates 0 words

private theorem batches_ok_iff (dates : List DateValues.Column) (words : List Narrow.Column) :
    Internal.narrowBatches dates = .ok words ↔
      words.map (List.map (Option.map Date32.toCivil)) = dates :=
  indexed_ok_iff (fun (batch, index) => Internal.narrowBatch index batch) _
    (fun batch index => batch_ok_iff index batch) dates 0 words

private theorem ofEpochDay?_eq_none_iff (day : Int) :
    Date32.ofEpochDay? day = none ↔ day < -2147483648 ∨ 2147483647 < day := by
  have bounds := Date32.ofEpochDay?_isSome_iff day
  cases word : Date32.ofEpochDay? day <;> simp [word] at bounds ⊢ <;> omega

private theorem slot_outOfRange_iff (index position batch slot : Nat)
    (date : Option CivilDate) (day : Int) :
    Internal.narrowSlot index position date = .error (.outOfRange batch slot day) ↔
      index = batch ∧ position = slot ∧
        ∃ civil, date = some civil ∧ civil.toEpochDay? = some day ∧
          (day < -2147483648 ∨ 2147483647 < day) := by
  cases date with
  | none => simp [Internal.narrowSlot]
  | some civil =>
    cases count : civil.toEpochDay? with
    | none => simp [Internal.narrowSlot, count]
    | some actual =>
      cases word : Date32.ofEpochDay? actual with
      | none =>
        have out := (ofEpochDay?_eq_none_iff actual).mp word
        simp only [Internal.narrowSlot, count, word, Except.error.injEq,
          Error.outOfRange.injEq, Option.some.injEq, exists_eq_left']
        constructor
        · rintro ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, out⟩
        · rintro ⟨rfl, rfl, rfl, _⟩
          exact ⟨rfl, rfl, rfl⟩
      | some word =>
        simp only [Internal.narrowSlot, count, word, Pure.pure, Except.pure,
          reduceCtorEq, false_iff, not_and, Option.some.injEq, exists_eq_left']
        intro _ _ same
        subst day
        intro out
        rw [(ofEpochDay?_eq_none_iff actual).mpr out] at word
        cases word

private theorem batch_outOfRange_iff (index : Nat) (dates : DateValues.Column)
    (batch slot : Nat) (day : Int) :
    Internal.narrowBatch index dates = .error (.outOfRange batch slot day) ↔
      index = batch ∧
        ∃ (earlierSlots suffix : DateValues.Column) (date : CivilDate),
          dates = earlierSlots ++ some date :: suffix ∧ earlierSlots.length = slot ∧
          (∃ words : Narrow.Column, words.map (Option.map Date32.toCivil) = earlierSlots) ∧
          date.toEpochDay? = some day ∧ (day < -2147483648 ∨ 2147483647 < day) := by
  rw [Internal.narrowBatch, indexed_error_iff]
  constructor
  · rintro ⟨earlierSlots, item, suffix, rfl, ⟨words, good⟩, failure⟩
    obtain ⟨same, position, date, rfl, dayEq, out⟩ := (slot_outOfRange_iff ..).mp failure
    exact ⟨same, earlierSlots, suffix, date, rfl, by simpa using position,
      ⟨words, (batch_ok_iff _ _ _).mp good⟩, dayEq, out⟩
  · rintro ⟨rfl, earlierSlots, suffix, date, rfl, position, ⟨words, good⟩, dayEq, out⟩
    exact ⟨earlierSlots, some date, suffix, rfl, ⟨words, (batch_ok_iff _ _ _).mpr good⟩,
      (slot_outOfRange_iff ..).mpr ⟨rfl, by simpa using position, date, rfl, dayEq, out⟩⟩

private theorem batches_outOfRange_iff (batches : List DateValues.Column)
    (batch slot : Nat) (day : Int) :
    Internal.narrowBatches batches = .error (.outOfRange batch slot day) ↔
      FirstOutOfRange batches batch slot day := by
  rw [Internal.narrowBatches, indexed_error_iff]
  constructor
  · rintro ⟨before, failed, after, rfl, ⟨words, earlier⟩, failure⟩
    obtain ⟨index, earlierSlots, suffix, date, rfl, position, inBatch, dayEq, out⟩ :=
      (batch_outOfRange_iff ..).mp failure
    exact ⟨before, after, earlierSlots, suffix, date, rfl, by simpa using index, position,
      ⟨words, (batches_ok_iff _ _).mp earlier⟩, inBatch, dayEq, out⟩
  · rintro ⟨before, after, earlierSlots, suffix, date, rfl, index, position,
      ⟨words, earlier⟩, inBatch, dayEq, out⟩
    exact ⟨before, _, after, rfl, ⟨words, (batches_ok_iff _ _).mpr earlier⟩,
      (batch_outOfRange_iff ..).mpr
        ⟨by simpa using index, earlierSlots, suffix, date, rfl, position, inBatch, dayEq, out⟩⟩

theorem read_ok_iff (limits : Limits) (input : KBytes) (output : Narrow.Stream) :
    Narrow.read limits input = .ok output ↔
      DateStream.read limits input =
        .ok ⟨⟨output.name, output.nullable, .millisecond⟩, civilBatches output⟩ := by
  cases output with
  | mk name nullable batches =>
    cases parsed : DateStream.read limits input with
    | error =>
      simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind]
    | ok source =>
      cases source with
      | mk field dates =>
        cases field with
        | mk originalName originalNullable unit =>
          cases unit with
          | day =>
            simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind]
          | millisecond =>
            cases converted : Internal.narrowBatches dates with
            | error cause =>
              have different : civilBatches ⟨name, nullable, batches⟩ ≠ dates := by
                intro same
                rw [(batches_ok_iff _ _).mpr same] at converted
                cases converted
              simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind, converted, Ne.symm different]
            | ok actual =>
              have exactDates := (batches_ok_iff _ _).mp converted
              have same : actual = batches ↔ civilBatches ⟨name, nullable, batches⟩ = dates := by
                constructor
                · rintro rfl
                  exact exactDates
                · intro expected
                  rw [(batches_ok_iff _ _).mpr expected] at converted
                  exact (Except.ok.inj converted).symm
              simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind, converted,
                Pure.pure, Except.pure, same, eq_comm (a := civilBatches _), and_assoc]

theorem read_outOfRange_iff (limits : Limits) (input : KBytes)
    (batch slot : Nat) (day : Int) :
    Narrow.read limits input = .error (.outOfRange batch slot day) ↔
      ∃ source, DateStream.read limits input = .ok source ∧ source.field.unit = .millisecond ∧
        FirstOutOfRange source.batches batch slot day := by
  cases parsed : DateStream.read limits input with
  | error => simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind]
  | ok source =>
    by_cases unit : source.field.unit = .millisecond
    · cases result : Internal.narrowBatches source.batches with
      | ok => simp [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind,
          result, Pure.pure, Except.pure, ← batches_outOfRange_iff]
      | error => simp [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind,
          result, ← batches_outOfRange_iff]
    · simp [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind]

private theorem wire_hasDay {limits : Limits} {input : KBytes} {field : DateStream.Field}
    {remaining offset : Nat} {batches : List DateValues.Column}
    (wire : BatchesWire limits input field remaining offset batches)
    (unit : field.unit = .millisecond) :
    ∀ batch ∈ batches, ∀ date, some date ∈ batch → ∃ day, date.toEpochDay? = some day := by
  induction wire with
  | eos => simp
  | @next fuel offset size next dates tail _ decoded _ ih =>
    intro batch belongs date present
    rcases List.mem_cons.mp belongs with same | later
    · subst batch
      obtain ⟨_, _, _, _, _, _, _, _, _, checked⟩ :=
        (DateStream.readBatch_iff limits input field offset size dates next).mp decoded
      obtain ⟨index, atIndex⟩ := List.mem_iff_get.mp present
      obtain ⟨valid, word, _, _, observed⟩ := checked.slot index
      rw [atIndex] at observed
      cases valid with
      | false => simp at observed
      | true =>
        obtain ⟨civil, encoded, same⟩ := observed
        have civilEq : date = civil := Option.some.inj same
        subst civil
        cases day : Date64.toEpochDay? (Int64.ofNat word) with
        | none => simp [DateStream.Field.decoder, DateBatch.dateDecoder, unit,
            DateValues.Unit.toCivil?, Date64.toCivil?, day] at encoded
        | some count =>
          have equal : CivilDate.ofEpochDay count = date := by
            simpa [DateStream.Field.decoder, DateBatch.dateDecoder, unit,
              DateValues.Unit.toCivil?, Date64.toCivil?, day] using encoded
          exact ⟨count, equal ▸ CivilDate.toEpochDay?_ofEpochDay count⟩
    · exact ih batch later date present

private theorem invalid_slot_exists {batches : List DateValues.Column} {batch slot : Nat}
    (failure : Internal.narrowBatches batches = .error (.invalidCivil batch slot)) :
    ∃ col ∈ batches, ∃ date, some date ∈ col ∧ date.toEpochDay? = none := by
  rw [Internal.narrowBatches, indexed_error_iff] at failure
  obtain ⟨before, col, after, rfl, _, inColumn⟩ := failure
  change Internal.narrowBatch (0 + before.length) col = .error (.invalidCivil batch slot) at inColumn
  rw [Internal.narrowBatch, indexed_error_iff] at inColumn
  obtain ⟨earlier, cell, later, rfl, _, inSlot⟩ := inColumn
  cases cell with
  | none => simp [Internal.narrowSlot] at inSlot
  | some date =>
    cases observed : date.toEpochDay? with
    | none => exact ⟨earlier ++ some date :: later, by simp, date, by simp, observed⟩
    | some day =>
      cases narrowed : Date32.ofEpochDay? day <;>
        simp [Internal.narrowSlot, observed, narrowed, Pure.pure, Except.pure] at inSlot

theorem read_ne_invalidCivil (limits : Limits) (input : KBytes) (batch slot : Nat) :
    Narrow.read limits input ≠ .error (.invalidCivil batch slot) := by
  intro failed
  cases parsed : DateStream.read limits input with
  | error => simp [Narrow.read, parsed, Except.mapError, Bind.bind, Except.bind] at failed
  | ok source =>
    by_cases unit : source.field.unit = .millisecond
    · cases result : Internal.narrowBatches source.batches with
      | ok => simp [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind,
          result, Pure.pure, Except.pure] at failed
      | error cause =>
        have same : cause = .invalidCivil batch slot := by
          simpa [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind, result] using failed
        subst cause
        obtain ⟨column, member, date, present, invalid⟩ := invalid_slot_exists result
        obtain ⟨_, _, _, wire⟩ := (DateStream.read_iff limits input source).mp parsed
        obtain ⟨day, dayEq⟩ := wire_hasDay wire unit column member date present
        rw [invalid] at dayEq
        cases dayEq
    · simp [Narrow.read, parsed, Except.mapError, unit, Bind.bind, Except.bind] at failed

end Silmaril.Proofs.Formats.Arrow.DateStream.Narrow
