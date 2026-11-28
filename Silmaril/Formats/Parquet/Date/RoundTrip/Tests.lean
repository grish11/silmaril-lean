module

meta import Silmaril.Formats.Parquet.Date.RoundTrip.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.RoundTrip

private meta def writerLimits : Date.FromIpc.Multi.Limits :=
  ⟨⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, 16, 32⟩

private meta def observe (wire : Bytes) : Option Observation := do
  let checked ← (Date.openChecked {} wire).toOption
  let groups ← ((List.range checked.snapshot.groupCount).mapM (checked.readGroup {})).toOption
  return ⟨checked.binding.leaf.name, checked.binding.leaf.repetition == some .optional,
    groups.map (·.date32Slots)⟩

private meta def roundtrip (expected : Observation) : Bool :=
  ((do
    let first ← (Arrow.DateStream.Writer.emit {} expected.name expected.nullable expected.batches).toOption
    let middle ← (Date.FromIpc.Multi.convert {} writerLimits {} first).toOption
    let second ← (Date.Events.ToIpc.convert {} {} middle).toOption
    let last ← (Date.FromIpc.Multi.convert {} writerLimits {} second).toOption
    let firstRead ← (Arrow.DateStream.read {} first).toOption
    let secondRead ← (Arrow.DateStream.read {} second).toOption
    let source ← observe middle
    let target ← observe last
    return firstRead == expected.ipc && secondRead == expected.ipc &&
      source == expected && target == expected
    : Option Bool)).getD false

#guard roundtrip ⟨"日付", true, [[], [some (-2147483648), none], [], [some 2147483647], []]⟩
#guard roundtrip ⟨"日付", false, [[], [some (-1), some 0], []]⟩
#guard roundtrip ⟨"日付", true, [[], [], []]⟩

#guard match Arrow.DateStream.Writer.emit {} "日付" true [] with
  | .error _ => false
  | .ok schemaOnly =>
    match Date.FromIpc.Multi.convert {} writerLimits {} schemaOnly with
    | .error (.source (.batchCount 0)) => true
    | _ => false
