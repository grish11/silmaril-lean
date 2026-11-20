module

public import Silmaril.Formats.Dasl.Resolve.Defs

/-! Deterministic, bounded observations of an already decoded store. Fuel counts
the number of CAS boundaries on a path, not the amount of inline syntax. -/

@[expose] public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type}

/-- Executable shallow storage. Readers of raw bytes must distinguish invalid wire
before constructing this decoded interface. -/
structure Reader (Name : Type) where
  object? : Name → Option (Shallow Name)
  blob? : Name → Option ByteArray

def Reader.store (reader : Reader Name) : Store Name :=
  ⟨graph reader.object?, graph reader.blob?⟩

/-- Traverse inline syntax and consult a policy at the immediate CAS boundaries.
No target is silently substituted on a failed read. -/
def Shallow.observeWith (objects : Name → Option (Partial Name)) (blobs : Name → Option ByteArray) :
    Shallow Name → Partial Name
  | .ref (.obj name) => match objects name with
    | none => .ref (.obj name)
    | some target => .obj name target
  | .ref (.blob name) => match blobs name with
    | none => .ref (.blob name)
    | some payload => .blob name payload
  | .obj impossible _ | .blob impossible _ => impossible.elim
  | .dict keys values => .dict keys fun key => observeWith objects blobs (values key)
  | .list len values => .list len fun index => observeWith objects blobs (values index)
  | .i64 bits => .i64 bits
  | .bytes payload => .bytes payload
  | .string text => .string text
  | .bool value => .bool value
  | .null => .null

/-- Zero fuel preserves the shallow view. At positive fuel, every successful immediate read
opens a link; object children have one less unit of fuel. Inline containers cost no fuel. -/
def Reader.observe (reader : Reader Name) : Nat → Shallow Name → Partial Name
  | 0 => Shallow.embed
  | fuel + 1 => Shallow.observeWith (fun name => (reader.object? name).map (reader.observe fuel)) reader.blob?

/-- The shallow root itself costs no fuel. A missing root returns `none`; a missing child
under a present root stays a named reference in the returned observation. -/
def Reader.observeRoot? (reader : Reader Name) (fuel : Nat) (root : Name) : Option (Partial Name) :=
  (reader.object? root).map (reader.observe fuel)

end Silmaril.Formats.Dasl
