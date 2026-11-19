module

public import Silmaril.Formats.JsonWithBytes.Traverse.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWithBytes.Traverse

open Silmaril.Formats Silmaril.Formats.JsonWithBytes

theorem uniqueKeys_iff {Key Atom : Type} [DecidableEq Key] {index : JsonIx}
    (value : RawSyn Key Atom index) : uniqueKeys value = true ↔ value.WellFormed := by
  induction value <;> simp_all [uniqueKeys]

end Silmaril.Proofs.Formats.JsonWithBytes.Traverse
