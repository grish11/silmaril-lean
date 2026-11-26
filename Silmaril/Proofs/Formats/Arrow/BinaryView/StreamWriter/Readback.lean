module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Arrow.BinaryView.StreamWriter

theorem emit_readback {ipc : Arrow.Limits} {limits : Column.Limits} {field : Schema.Field}
    {batches : List (Schema.Values field.kind)} {wire : KBytes}
    (written : emit ipc limits field batches = .ok wire) :
    ∃ decoded, Stream.read ipc limits wire = .ok decoded ∧ Agrees field batches decoded := by
  cases serialized : serialize ipc limits field batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases decoded : Stream.read ipc limits actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      by_cases agrees : Agrees field batches result
      · have same : actual = wire := by
          simpa [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] using written
        exact ⟨result, same ▸ decoded, agrees⟩
      · simp [emit, serialized, decoded, agrees, Bind.bind, Except.bind, Except.mapError] at written

theorem emit_binary_readback {ipc : Arrow.Limits} {limits : Column.Limits} {name : String}
    {nullable : Bool} {batches : List (List (Option KBytes))} {wire : KBytes}
    (written : emit ipc limits ⟨name, nullable, .binary⟩ batches = .ok wire) :
    ∃ decoded : List (List (Option KBytes)),
      Stream.read ipc limits wire = .ok ⟨⟨name, nullable, .binary⟩, decoded⟩ ∧
        decoded.map (List.map (Option.map KBytes.toList)) =
          batches.map (List.map (Option.map KBytes.toList)) := by
  obtain ⟨⟨actual, values⟩, read, same, agrees⟩ := emit_readback written
  change actual = ⟨name, nullable, .binary⟩ at same
  subst actual
  exact ⟨values, read, agrees⟩

theorem emit_utf8_readback {ipc : Arrow.Limits} {limits : Column.Limits} {name : String}
    {nullable : Bool} {batches : List (List (Option String))} {wire : KBytes}
    (written : emit ipc limits ⟨name, nullable, .utf8⟩ batches = .ok wire) :
    Stream.read ipc limits wire = .ok ⟨⟨name, nullable, .utf8⟩, batches⟩ := by
  obtain ⟨⟨actual, values⟩, read, same, agrees⟩ := emit_readback written
  change actual = ⟨name, nullable, .utf8⟩ at same
  subst actual
  change values.map (fun slots => slots) = batches.map (fun slots => slots) at agrees
  have sameValues : values = batches := by simpa using agrees
  simpa [sameValues] using read

end Silmaril.Proofs.Formats.Arrow.BinaryView.StreamWriter
