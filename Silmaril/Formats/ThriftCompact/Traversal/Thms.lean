module

public import Silmaril.Formats.ThriftCompact.Traversal.Defs
import Silmaril.Proofs.Formats.ThriftCompact.Traversal.Stop

public section

namespace Silmaril.Formats.ThriftCompact.Traversal

/-- A successful struct traversal returns the first offset after a STOP octet. -/
theorem readStruct_stop {reader : Reader} {offset next : Nat} {fields : List Field}
    (parsed : readStruct reader offset = .ok (fields, next)) :
    ∃ stop, next = stop + 1 ∧ reader.source.data[stop]? = some 0 :=
  Proofs.Formats.ThriftCompact.Traversal.readStruct_stop parsed

end Silmaril.Formats.ThriftCompact.Traversal
