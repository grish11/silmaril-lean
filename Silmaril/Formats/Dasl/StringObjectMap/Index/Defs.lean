module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Formats.Dasl.StringObjectMap.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.StringObjectMap.Index

open Silmaril.Semantics.Prolly (Policy)

variable {Name : Type}

abbrev Block (Name : Type) := Semantics.Prolly.Block Name String (Placement Name)

def blockCodec : Encode.PartialCodec (Block Name) (Shallow Name) :=
  Prolly.blockCodec Encode.text Placement.codec

abbrev build (policy : Policy String) (layout : Layout Name) := Semantics.Prolly.build policy layout

inductive Fault (Name : Type) where
  | index (fault : Prolly.Fault Name)
  | value (fault : ValueFault Name)
  deriving DecidableEq, Repr

/-- The index uses Prolly's closed-view scan, not a routed lookup. It recovers
the value placement first, then reads an external value only if requested. -/
def lookup (read : Read Name) (width fuel : Nat) (root : Name) (key : String) :
    Except (Fault Name) (Option (Shallow Name)) :=
  match Prolly.lookup blockCodec read width fuel root key with
  | .error fault => .error (.index fault)
  | .ok placement => match recover read placement with
    | .error fault => .error (.value fault)
    | .ok value => .ok value

end Silmaril.Formats.Dasl.StringObjectMap.Index
