module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming

variable {Name Payload : Type}

def listed (writes : List (Name × Payload)) : Relation Name Payload := fun name payload => (name, payload) ∈ writes

def admitOne [DecidableEq Name] [DecidableEq Payload] (read : Name → Option Payload) (write : Name × Payload) :
    Except Name (Name → Option Payload) :=
  match read write.1 with
  | none => .ok (fun name => if name = write.1 then some write.2 else read name)
  | some present => if present = write.2 then .ok read else .error write.1

/-- Pure batch admission. Run on an authoritative snapshot, not on a filtered or
partial reader that can mislabel existing bytes as missing. No partial write is
returned on error, and an exact repeat is idempotent. -/
def admit [DecidableEq Name] [DecidableEq Payload] (read : Name → Option Payload) :
    List (Name × Payload) → Except Name (Name → Option Payload)
  | [] => .ok read
  | write :: rest => match admitOne read write with
    | .ok staged => admit staged rest
    | .error name => .error name

end Silmaril.Semantics.Naming
