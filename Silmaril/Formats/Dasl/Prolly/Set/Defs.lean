module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedSet)
open Silmaril.Semantics.Prolly (Block)
open Silmaril.Semantics.Naming (Relation)

variable {Name Key : Type} [LinearOrder Key]

def setCodec (key : Encode.TotalCodec Key (Shallow Name)) : Encode.PartialCodec (Block Name Key Unit) (Shallow Name) :=
  blockCodec key Encode.null

def closedSet (codec : Encode.PartialCodec (Block Name Key Unit) (Shallow Name))
    (read : Read Name) (width fuel : Nat) (root : Name) : Except (Fault Name) (OrderedSet Key) :=
  closedMap codec read width fuel root

/-- A successful complete read represents an extensional set. Errors are not sets. -/
def setNames (codec : Encode.PartialCodec (Block Name Key Unit) (Shallow Name))
    (read : Read Name) (width fuel : Nat) : Relation Name (Finset Key) :=
  fun root keys => ∃ view, closedSet codec read width fuel root = .ok view ∧ view.keys.toFinset = keys

end Silmaril.Formats.Dasl.Prolly
