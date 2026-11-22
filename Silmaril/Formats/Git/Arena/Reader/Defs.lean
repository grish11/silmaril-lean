module

public import Silmaril.Formats.Git.Arena.Defs
public import Silmaril.Formats.Dasl.Prolly.Route.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Arena

variable {Name Payload Value : Type} {limit : Nat}

abbrev CasReader (Name : Type) := CasLane → Name → Read ByteArray

def State.casReader [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) : CasReader Name := fun lane name => arena.readCas profile lane name

/-- A typed read description, not a proof that a name has been bound. It has
no slot/key, Git name, or dependency on a particular reader or storage layout. -/
structure Descriptor (Name Value : Type) where
  lane : CasLane
  name : Name
  decode : ByteArray → Option Value

def Descriptor.raw (name : Name) : Descriptor Name ByteArray := ⟨.raw, name, some⟩

def Descriptor.object (name : Name) (decode : ByteArray → Option Value) : Descriptor Name Value :=
  ⟨.object, name, decode⟩

/-- A decode error is invalid, not missing. Every non-hit is preserved. -/
def Descriptor.read (descriptor : Descriptor Name Value) (read : CasReader Name) : Read Value :=
  (read descriptor.lane descriptor.name).andThen fun bytes =>
    match descriptor.decode bytes with
    | some value => .found value
    | none => .invalid

inductive ReadFault where
  | unindexed | placeholder | missing | deferred | invalid | conflict | unavailable
  deriving DecidableEq, Repr

def Read.toExcept (result : Read Value) : Except ReadFault Value :=
  match result with
  | .unindexed => .error .unindexed
  | .placeholder => .error .placeholder
  | .missing => .error .missing
  | .deferred => .error .deferred
  | .invalid => .error .invalid
  | .conflict => .error .conflict
  | .unavailable => .error .unavailable
  | .found value => .ok value

open Silmaril.Semantics.Prolly (Block)

/-- Fits the existing Prolly typed reader. Arena failures are classified by
the consumer because the landed Prolly fault type has no defer/conflict tag.
Successful parsing is not evidence of byte/name binding. -/
def CasReader.prolly {Key Item : Type} (read : CasReader Name) (parse : ByteArray → Option (Dasl.Shallow Name))
    (codec : Dasl.Encode.PartialCodec (Block Name Key Item) (Dasl.Shallow Name))
    (classify : Name → ReadFault → Dasl.Prolly.Fault Name)
    (name : Name) : Except (Dasl.Prolly.Fault Name) (Block Name Key Item) := do
  let bytes ← (read .object name).toExcept.mapError (classify name)
  Dasl.Prolly.readBlock codec (fun _ => match parse bytes with
    | none => .invalidWire
    | some shallow => .found shallow) name

/-- Exact byte intake. A decoder accepting an alternate spelling must not
silently replace the observed bytes when the payload is cached under this ID. -/
def Reader.exact (profile : Profile Name Payload) (decode : Id Name → ByteArray → Option Payload)
    (fetch : Reader Name ByteArray) : Reader Name Payload := fun id =>
  match fetch id with
  | .missing => .missing
  | .deferred => .deferred
  | .invalid => .invalid
  | .conflict => .conflict
  | .found bytes =>
    match decode id bytes with
    | none => .invalid
    | some payload => if profile.wire id payload = some bytes then .found payload else .invalid

def State.cacheBytes [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (key : Fin limit) (id : Id Name)
    (decode : Id Name → ByteArray → Option Payload) (fetch : Reader Name ByteArray) :
    Except Fault (Payload × State limit Name Payload) :=
  arena.cache profile key id (Reader.exact profile decode fetch)

structure Loaded (limit : Nat) (Name Payload : Type) where
  payload : Payload
  derivation : Except Fault (Id Name)
  arena : State limit Name Payload

/-- Fetch/validate first. A failure to derive or attach a second lane's name
does not lose the successfully cached content or commit a second binding. -/
def State.cacheAndAssign [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (key : Fin limit) (id : Id Name) (lane : Lane)
    (decode : Id Name → ByteArray → Option Payload) (fetch : Reader Name ByteArray) :
    Except Fault (Loaded limit Name Payload) := do
  let (payload, cached) ← arena.cacheBytes profile key id decode fetch
  match cached.assign profile key lane with
  | .error fault => pure ⟨payload, .error fault, cached⟩
  | .ok (derived, after) => pure ⟨payload, .ok derived, after⟩

end Silmaril.Formats.Git.Arena
