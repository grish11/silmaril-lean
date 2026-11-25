module
public import Silmaril.Formats.Sqlite.Varint.Defs
import Silmaril.Proofs.Formats.Sqlite.Varint
import Silmaril.Proofs.Formats.Sqlite.Varint.Nine

public section
namespace Silmaril.Formats.Sqlite.Varint

theorem readAux?_progress (view : File.View) (fuel offset acc value next : Nat)
    (parsed : readAux? view fuel offset acc = some (value,next)) :
    offset < next ∧ next ≤ offset + fuel :=
  Silmaril.Proofs.Formats.Sqlite.Varint.readAux?_progress view fuel offset acc value next parsed

/-- A successful SQLite varint consumes at least one and at most nine octets,
including its distinct full-octet ninth position. -/
theorem read?_progress (view : File.View) (offset next : Nat) (value : UInt64)
    (parsed : read? view offset = some (value,next)) :
    offset < next ∧ next ≤ offset + 9 :=
  Silmaril.Proofs.Formats.Sqlite.Varint.read?_progress view offset next value parsed

/-- A view containing the encoder's nine octets decodes to the exact value
and the offset just after the ninth octet. Only those nine octets are required. -/
theorem read?_encode_nine (view : File.View) (offset : Nat) (value : UInt64)
    (high : 2 ^ 56 ≤ value.toNat)
    (bytes : ∀ i, i < 9 → view.get? (offset + i) = (encode value).toList[i]?) :
    read? view offset = some (value, offset + 9) :=
  Silmaril.Proofs.Formats.Sqlite.Varint.Nine.read_encode view offset value high bytes

end Silmaril.Formats.Sqlite.Varint
