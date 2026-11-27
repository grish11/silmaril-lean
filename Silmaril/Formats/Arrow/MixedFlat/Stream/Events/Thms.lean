module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Events.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Events

open MixedFlat.Events

/-- EOS requires a complete modern EOS frame at the end of the carrier. -/
theorem readNext_eos {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining ordinal rows offset : Nat} :
    readNext limits input fields remaining ordinal rows offset = .ok none ↔
      readEnvelope limits.observation.ipc input offset = .ok .eos ∧ offset + 8 = input.len :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Events.readNext_eos

/-- The immutable pull step removes exactly one original eager record. -/
theorem readNext_record {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining ordinal rows offset : Nat} {decoded : Decoded fields}
    (step : readNext limits input fields remaining ordinal rows offset = .ok (some decoded)) :
    ∃ fuel, remaining = fuel + 1 ∧
      Stream.readBatches limits input fields remaining ordinal rows offset =
        (Stream.readBatches limits input fields fuel (ordinal + 1)
          (rows + decoded.record.observed.rowCount) decoded.record.range.next).map
          (List.cons decoded.record) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Events.readNext_record step

/-- One message ordinal per delivered event, including an empty batch. -/
theorem Prefix.ordinal {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining first rows offset : Nat} {events : List (MixedFlat.Events.Batch (schema fields))}
    {available last finalRows finalOffset : Nat}
    (delivered : Prefix limits input fields remaining first rows offset events
      available last finalRows finalOffset) :
    last = first + events.length := by
  induction delivered <;> simp_all [Nat.add_assoc, Nat.add_comm]

/-- Successful drain agrees with the eager stream reader in schema, exact
ordered events and EOS. A post-open error retains the completed original
prefix and identifies the next attempted ordinal, offset and eager cause. -/
theorem readAll_exact (limits : MixedFlat.Limits) (input : KBytes) :
    match admit limits input with
    | .error error =>
        readAll limits input = .error error ∧ Stream.read limits input = .error error.eager
    | .ok (fields, start) =>
      ∃ trace : Trace (schema fields), readAll limits input = .ok ⟨schema fields, trace⟩ ∧
        match Stream.read limits input with
        | .ok eager => eager.fields = fields ∧ trace.termination = .eos ∧
            List.Forall₂ (fun record => Agrees (schema fields) record.observed) eager.batches trace.batches
        | .error eagerError =>
          ∃ available ordinal rows offset cause,
            Prefix limits input fields limits.observation.ipc.batches 0 0 start trace.batches
              available ordinal rows offset ∧
            readNext limits input fields available ordinal rows offset =
              .error (.message ordinal offset cause) ∧
            eagerError = .batch ordinal cause ∧ trace.termination = .readError (.message ordinal offset cause) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Events.readAll_exact limits input

end Silmaril.Formats.Arrow.MixedFlat.Stream.Events
