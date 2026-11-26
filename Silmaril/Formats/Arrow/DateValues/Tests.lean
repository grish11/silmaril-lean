module

import Silmaril.Formats.Arrow.DateValues.Thms
meta import Silmaril.Formats.Arrow.DateValues.Defs

/-! Executable DATE metadata, validity, range, and slice controls. -/

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateValues

private meta def day : Descriptor := ⟨8, 0, 0, true⟩
private meta def millis : Descriptor := ⟨8, 1, 0, true⟩

private meta def sliced : View :=
  ⟨1, ⟨3, 1⟩, .leaf 1 0xd, .leaf 16 (99 * 2^32 + 0xffffffff * 2^64 + 11016 * 2^96)⟩

#guard decode {} .day day sliced = .ok [none, some ⟨1969, 12, 31⟩, some ⟨2000, 2, 29⟩]
#guard decode {} .day { day with nullable := false } sliced = .error (.ipc (.malformed .validityBitmap))
#guard decode {} .day { day with endianness := 1 } sliced = .error (.ipc (.unsupported (.endianness 1)))
#guard decode {} .day { day with typeTag := 2 } sliced = .error (.ipc (.unsupported (.fieldType 2)))
#guard decode {} .day millis sliced = .error (.wrongUnit .day 1)
#guard decode {} .millisecond { millis with dateUnit := 2 } sliced = .error (.wrongUnit .millisecond 2)
#guard decode {} .day day { sliced with start := 2 } = .error (.ipc (.malformed .bodyValues))
#guard decode {} .day day { sliced with start := 7 } = .error (.ipc (.malformed .validityBitmap))
#guard decode {} .day day { sliced with node := ⟨3, 0⟩ } = .error (.ipc (.malformed .validityBitmap))
#guard decode { rows := 2 } .day day sliced = .error (.ipc (.limit .rows))
#guard decode {} .day day { sliced with values := .node 16 (.leaf 1 0) (.leaf 1 0) } =
  .error (.ipc (.malformed .source))
#guard decode {} .day day ⟨0, ⟨1, 0⟩, .empty, .leaf 4 0xffffffff⟩ = .ok [some ⟨1969, 12, 31⟩]

private meta def partialMilliseconds : View :=
  ⟨0, ⟨2, 1⟩, .leaf 1 1, .leaf 16 ((2^64 - 86400000) + 2^64)⟩

#guard decode {} .millisecond millis partialMilliseconds = .ok [some ⟨1969, 12, 31⟩, none]
#guard decode {} .millisecond millis { partialMilliseconds with node := ⟨2, 0⟩, validity := .empty } =
  .error (.nonWholeDay 1)
#guard decode {} .millisecond millis { partialMilliseconds with values := .leaf 15 0 } =
  .error (.ipc (.malformed .bodyValues))

private meta def batch : RecordBatch := ⟨3, [⟨3, 1⟩], [⟨0, 1⟩, ⟨8, 12⟩]⟩

private meta def body : KBytes :=
  .leaf 24 (5 + (0xffffffff + 11016 * 2^64) * 2^64)

#guard DateValues.decodeBatch {} .day day batch body = .ok [some ⟨1969, 12, 31⟩, none, some ⟨2000, 2, 29⟩]
#guard DateValues.decodeBatch {} .day day { batch with rowCount := 4 } body = .error (.ipc (.malformed .batchLayout))
#guard DateValues.decodeBatch {} .day day { batch with buffers := [⟨0, 1⟩, ⟨8, 17⟩] } body =
  .error (.ipc (.malformed .batchLayout))
#guard DateValues.decodeBatch {} .day day { batch with buffers := [⟨0, 1⟩, ⟨4, 12⟩] } body =
  .error (.ipc (.malformed .batchLayout))
#guard DateValues.decodeBatch {} .day day { batch with buffers := [⟨0, 9⟩, ⟨8, 12⟩] } body =
  .error (.ipc (.malformed .batchLayout))
#guard DateValues.decodeBatch {} .day day { batch with buffers := [⟨0, 1⟩] } body =
  .error (.ipc (.malformed .batchLayout))
#guard DateValues.decodeBatch {} .day day { batch with buffers := [⟨0, 1⟩, ⟨8, 8⟩] } body =
  .error (.ipc (.malformed .bodyValues))
