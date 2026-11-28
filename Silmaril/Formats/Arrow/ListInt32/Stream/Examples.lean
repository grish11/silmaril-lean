module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Arrow.ListInt32.Stream.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Arrow.ListInt32.Stream.Defs

namespace Silmaril.Formats.Arrow.ListInt32.Stream

private def native : KBytes :=
  let bytes := include_bytes "../../../../../data/arrow-list-int32-stream/nullable-list-int32.arrows"
  .leaf bytes.size (KBytes.leVal bytes.data.toList)

private def first : List Row := [none, some [], some [some (-7), none, some 0], some [none]]

private def last : List Row := [some [], some [some (-2147483648), some 2147483647]]

private def change (source : KBytes) (offset value : Nat) : KBytes :=
  source.slice 0 offset ++ .leaf 1 value ++ source.slice (offset + 1) (source.len - offset - 1)

set_option synthInstance.maxSize 1024

#guard read {} native = .ok ⟨⟨"items", "element"⟩, [
  ⟨184, 184, 64, 5, first⟩,
  ⟨440, 176, 8, 0, []⟩,
  ⟨632, 184, 24, 2, last⟩]⟩

-- The parent bitmap masks physical child 99. It still counts toward the budget.
#guard read { totalChildren := 4 } native = .error (.batch 0 .childLimit)
#guard read { totalChildren := 6 } native = .error (.batch 2 .childLimit)
#guard read { totalRows := 5 } native = .error (.batch 2 .rowLimit)
#guard read { ipc.batches := 1 } native = .error (.batch 1 .batchLimit)

#guard read {} (change native 176 64) = .error (.schemaMetadata (.unsupported .fieldInteger))
#guard read {} (change native 376 15) = .error (.batch 0 .parentValidity)
#guard read {} (change native 408 27) = .error (.batch 0 (.child (.malformed .validityBitmap)))
#guard read {} (change native 388 2) = .error (.batch 0 .offsets)
#guard read {} (change native 391 128) = .error (.batch 0 .offsets)
#guard read {} (change native 392 6) = .error (.batch 0 .offsets)
#guard read {} (change native 400 4) = .error (.batch 0 .offsets)
#guard read {} (change native 320 56) = .error (.batch 0 .layout)

#guard read {} (native.slice 0 184 ++ native.slice 848 8) =
  .ok ⟨⟨"items", "element"⟩, []⟩
#guard read {} (native.slice 0 847) = .error (.batch 2 (.body (.malformed .truncated)))
#guard read {} (native.slice 0 848) = .error (.batch 3 (.envelope (.malformed .truncated)))
#guard read {} (native ++ .leaf 1 0) = .error (.batch 3 .trailingBytes)

-- The shared flat reader retains its original nested-field refusal.
#guard (Arrow.readStream {} native).map (·.fields) = .error (.unsupported (.fieldType 12))

end Silmaril.Formats.Arrow.ListInt32.Stream
