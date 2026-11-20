module

public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.RawStore

open Silmaril.Semantics.Naming

abbrev Blocks (Name : Type) := Relation Name ByteArray

/-- Separate the two codec domains and interpret only object blocks. Integrity is a
separate policy on the original bytes, not a property inferred from successful decoding. -/
structure Decoder (Name : Type) where
  objectName : Name → Prop
  rawName : Name → Prop
  disjoint : ∀ ⦃name⦄, objectName name → rawName name → False
  parse? : ByteArray → Option (Shallow Name)

def Decoder.view {Name : Type} (decoder : Decoder Name) (blocks : Blocks Name) : Store Name where
  objects name value := decoder.objectName name ∧ ∃ bytes, blocks name bytes ∧ decoder.parse? bytes = some value
  blobs name bytes := decoder.rawName name ∧ blocks name bytes

/-- Fill only genuinely absent names. Presence is tested on raw blocks, before decoding
or verification, so a malformed block cannot be displaced by a valid default. -/
abbrev fill {Name : Type} (base defaults : Blocks Name) : Blocks Name := fillMissing base defaults

/-- A binding extension of original bytes, respecting a caller-supplied policy on every
binding and admitting a finite full expansion from the indicated root. -/
def Completes {Name : Type} (decoder : Decoder Name) (policy : Blocks Name)
    (base extended : Blocks Name) (root : Name) : Prop :=
  Subset base extended ∧ Binding extended ∧ Subset extended policy ∧
    ∃ target, FullNames (decoder.view extended) root target

end Silmaril.Formats.Dasl.RawStore
