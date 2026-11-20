module

public import Silmaril.Formats.JsonWithBytes.Traverse.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Traverse

@[expose] public section

namespace Silmaril.Formats.JsonWithBytes

theorem uniqueKeys_iff {Key Atom : Type} [DecidableEq Key] {index : JsonIx}
    (value : RawSyn Key Atom index) : uniqueKeys value = true ↔ value.WellFormed :=
  Proofs.Formats.JsonWithBytes.Traverse.uniqueKeys_iff value

end Silmaril.Formats.JsonWithBytes
