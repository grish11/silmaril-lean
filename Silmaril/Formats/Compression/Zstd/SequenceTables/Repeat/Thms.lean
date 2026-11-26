module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables.Repeat.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat

/-- A state may start with no previous tables. -/
theorem empty_valid : State.empty.Valid := by
  simp [State.Valid, State.table, State.empty_previous]

/-- Repeat consumes zero description bytes and requires the previous
    table of the selected alphabet. -/
theorem resolveTable_repeat (prior : State) (alphabet : FseTable.Alphabet) (input : List UInt8) :
    resolveTable prior alphabet 3 input =
      match prior.table alphabet with
      | none => .error (.missingTable alphabet)
      | some table => .ok (table, input) := rfl

/-- Every resolved table has exact description bytes and comes from either
    an independently checked fresh description or the matching prior slot. -/
theorem resolveTable_sound {prior : State} {alphabet : FseTable.Alphabet} {mode : Nat}
    {input rest : List UInt8} {table : Table}
    (success : resolveTable prior alphabet mode input = .ok (table, rest)) :
    ∃ used, input = used ++ rest ∧ SelectionWire prior alphabet mode used rest table :=
  Proofs.Formats.Compression.Zstd.SequenceTables.Repeat.resolveTable_sound success

/-- The wire splits at the exact reverse suffix, with both caps enforced.
    Empty sections preserve state. A positive count proposes precisely
    the three tables selected in this section. -/
theorem resolve_sound {limits : Limits} {prior next : State} {input : List UInt8} {result : Section}
    (success : resolve limits prior input = .ok (result, next)) :
    input.length ≤ limits.inputBytes ∧ result.count ≤ limits.sequences ∧
      SectionWire prior input result ∧ StateUpdate prior result next :=
  Proofs.Formats.Compression.Zstd.SequenceTables.Repeat.resolve_sound success

/-- Each table in a successor state retains fresh wire provenance in
    the correct alphabet, by induction from the empty state. -/
theorem resolve_preserves_valid {limits : Limits} {prior next : State} {input : List UInt8}
    {result : Section} (valid : prior.Valid)
    (success : resolve limits prior input = .ok (result, next)) : next.Valid :=
  Proofs.Formats.Compression.Zstd.SequenceTables.Repeat.resolve_preserves_valid valid success

theorem suffix_exact {prior : State} {input : List UInt8} {result : Section}
    (wire : SectionWire prior input result) :
    input.drop (input.length - result.bitstream.length) = result.bitstream :=
  Proofs.Formats.Compression.Zstd.SequenceTables.Repeat.suffix_exact wire

end Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat
