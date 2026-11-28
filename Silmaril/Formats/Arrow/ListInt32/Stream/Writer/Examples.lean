module

import Batteries.Data.Except
import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Thms
meta import Batteries.Data.Except
meta import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs

namespace Silmaril.Formats.Arrow.ListInt32.Stream.Writer

private def field : ListInt32.Field := ⟨"items", "élément"⟩

private def first : List Row := [none, some [], some [none], some [some (-7), none, some 0]]

private def batches : List (List Row) := [first, [], [some [some (-2147483648), some 2147483647]]]

set_option synthInstance.maxSize 4096

#guard match emit {} field batches with
  | .ok wire =>
    match Stream.read {} wire with
    | .ok value => decide (Agrees field batches value) &&
      value.batches.map (·.bodyLength) == [56, 8, 32] &&
      (wire.slice (wire.len - 8) 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]
    | .error _ => false
  | .error _ => false

#guard match emit { ipc.fields := 1 } ⟨"", ""⟩ [] with
  | .ok wire => decide (Stream.read { ipc.fields := 1 } wire = .ok ⟨⟨"", ""⟩, []⟩)
  | .error _ => false

#guard offsetWords first = [0, 0, 0, 1, 4]
#guard childSlots first = [none, some (-7), none, some 0]
#guard checkRecord { bodyBytes := 2^36 } 1 (2^31 - 1) = .ok ()
#guard checkRecord { bodyBytes := 2^36 } 1 (2^31) = .error .offsetOverflow
#guard checkRecord { rows := 2^63 } (2^63) 0 = .error (.ipc (.malformed .flatbuffer))
#guard checkRecord { rows := 2^62 } (2^62) 0 = .error (.ipc (.malformed .bodyLength))
#guard checkRecord { metadataBytes := 199 } 0 0 = .error (.ipc (.limit .metadataBytes))

#guard (emit { ipc.fields := 0 } field []).map (fun _ => ()) = .error (.ipc (.limit .fields))
#guard (emit { ipc.fields := 1 } field [[]]).map (fun _ => ()) = .error (.record 0 (.ipc (.limit .fields)))
#guard (emit { ipc.metadataBytes := 64 } field []).map (fun _ => ()) = .error (.ipc (.limit .metadataBytes))
#guard (emit { ipc.batches := 2 } field batches).map (fun _ => ()) = .error (.ipc (.limit .batches))
#guard (emit { ipc.rows := 3 } field batches).map (fun _ => ()) = .error (.record 0 (.ipc (.limit .rows)))
#guard (emit { ipc.bodyBytes := 55 } field batches).map (fun _ => ()) =
  .error (.record 0 (.ipc (.limit .bodyBytes)))
#guard (emit { totalRows := 4 } field batches).map (fun _ => ()) = .error .rowLimit
#guard (emit { totalChildren := 5 } field batches).map (fun _ => ()) = .error .childLimit

end Silmaril.Formats.Arrow.ListInt32.Stream.Writer
