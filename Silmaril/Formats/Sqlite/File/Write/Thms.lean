module
public import Silmaril.Formats.Sqlite.File.Write.Defs
import Silmaril.Proofs.Formats.Sqlite.File.Write.TwoByte

public section
namespace Silmaril.Formats.Sqlite.File.Write

/-- Reading a two-byte field of a view recovers the writer's exact value when
it fits in the field and both view-relative byte reads match the encoding. -/
theorem be?_be_two (view : View) (offset value : Nat) (fits : value < 256 ^ 2)
    (bytes : ∀ i, i < 2 → view.get? (offset + i) = (be 2 value)[i]?) :
    view.be? offset 2 = some value :=
  Silmaril.Proofs.Formats.Sqlite.File.Write.be?_be_two view offset value fits bytes

/-- A two-byte read fails when its second byte lies outside the view. -/
theorem be?_two_truncated (view : View) (offset : Nat)
    (truncated : view.length < offset + 2) : view.be? offset 2 = none :=
  Silmaril.Proofs.Formats.Sqlite.File.Write.be?_two_truncated view offset truncated

/-- The two-byte page-size field of the actual database header stores 512. -/
theorem header_pageSize :
    (View.ofBytes (Bytes.ofList header)).be? 16 2 = some pageSize :=
  Silmaril.Proofs.Formats.Sqlite.File.Write.header_pageSize

end Silmaril.Formats.Sqlite.File.Write
