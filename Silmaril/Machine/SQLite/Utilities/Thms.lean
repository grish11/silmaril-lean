module

public import Silmaril.Machine.SQLite.Utilities.Defs
public import Silmaril.Formats.Sqlite.Varint.Thms
public import Silmaril.Formats.Sqlite.Varint.Exact.Thms

public section

namespace Silmaril.Machine.SQLite.Utilities

open Silmaril.Formats.Sqlite

/-- Every successful read advances by one to nine bytes. For a view containing
the encoded value at the given offset, the returned value and offset are exact. -/
theorem varint_roundtrip (view : File.View) (offset : Nat) (value : UInt64)
    (bytes : ∀ i, i < (Varint.encode value).toList.length →
      view.get? (offset + i) = (Varint.encode value).toList[i]?) :
    let next := offset + (Varint.encode value).toList.length
    Varint.read? view offset = some (value, next) ∧ offset < next ∧ next ≤ offset + 9 :=
  let decoded := Varint.read?_encode view offset value bytes
  ⟨decoded, Varint.read?_progress view offset _ value decoded⟩

end Silmaril.Machine.SQLite.Utilities
