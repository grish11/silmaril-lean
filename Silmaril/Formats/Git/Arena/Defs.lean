module

public import Silmaril.Formats.Git.Native.Defs
public import Silmaril.Semantics.Arena.Defs
public import Silmaril.Formats.Dasl.Arena.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Arena

open Silmaril.Semantics

/-- The algorithm tag is part of the address. Width is not evidence of binding. -/
inductive Oid where
  | sha1 (bytes : Native.NameBytes .sha1)
  | sha256 (bytes : Native.NameBytes .sha256)
  deriving DecidableEq

def Oid.algorithm : Oid → Native.Algorithm
  | .sha1 _ => .sha1
  | .sha256 _ => .sha256

def Oid.ofBytes : (algorithm : Native.Algorithm) → Native.NameBytes algorithm → Oid
  | .sha1 => .sha1
  | .sha256 => .sha256

inductive CasLane where
  | raw | object
  deriving DecidableEq, Repr

inductive Lane where
  | git (algorithm : Native.Algorithm)
  | cas (lane : CasLane)
  deriving DecidableEq

inductive Id (Name : Type) where
  | git (oid : Oid)
  | cas (lane : CasLane) (name : Name)
  deriving DecidableEq

def Id.lane {Name : Type} : Id Name → Lane
  | .git oid => .git oid.algorithm
  | .cas lane _ => .cas lane

/-- Serializers and name functions are independent, directional and partial.
When computation is unavailable, `attest` is the explicit external validation
hook. A computed mismatch takes precedence over it. -/
structure Profile (Name Payload : Type) where
  kind : Payload → Option Kind
  gitBytes : Native.Algorithm → Payload → Option ByteArray
  gitHash : (algorithm : Native.Algorithm) → ByteArray → Option (Native.NameBytes algorithm)
  casBytes : CasLane → Payload → Option ByteArray
  casName : CasLane → ByteArray → Option Name
  attest : Id Name → Payload → Bool := fun _ _ => false

variable {Name Payload : Type} {limit : Nat}

def Profile.derive (profile : Profile Name Payload) (lane : Lane) (payload : Payload) : Option (Id Name) :=
  match lane with
  | .git algorithm => do
    let _ ← profile.kind payload
    let bytes ← profile.gitBytes algorithm payload
    return .git (Oid.ofBytes algorithm (← profile.gitHash algorithm bytes))
  | .cas lane => do
    let bytes ← profile.casBytes lane payload
    return .cas lane (← profile.casName lane bytes)

def Profile.accepts [DecidableEq Name] (profile : Profile Name Payload) (id : Id Name) (payload : Payload) : Bool :=
  let kindOK := match id with | .git _ => (profile.kind payload).isSome | .cas _ _ => true
  kindOK && (match profile.derive id.lane payload with
    | some derived => decide (derived = id)
    | none => profile.attest id payload)

def Profile.wire (profile : Profile Name Payload) (id : Id Name) (payload : Payload) : Option ByteArray :=
  match id with
  | .git oid => profile.gitBytes oid.algorithm payload
  | .cas lane _ => profile.casBytes lane payload

/-- For a resident native object, not for an opaque reference. Reuses the
restricted native serializer; naming the children is an input to that codec. -/
def nativeObjectBytes {algorithm : Native.Algorithm} {Key Ref : Type} {kind : Kind}
    (profile : Native.Profile algorithm Key Ref) (object : Object Key Ref Native.CommitMetadata kind) :
    Option ByteArray :=
  match Native.renderObject profile object with
  | some (.encoded bytes) => some bytes
  | _ => none

structure Claims (Name : Type) where
  ids : List (Id Name) := []
  kind : Option Kind := none

def Claims.attach [DecidableEq Name] (claims : Claims Name) (id : Id Name) (kind : Option Kind) : Claims Name :=
  ⟨if id ∈ claims.ids then claims.ids else id :: claims.ids, claims.kind.or kind⟩

abbrev Cell (Name Payload : Type) := Semantics.Arena.Slot (Claims Name) Payload
abbrev State (limit : Nat) (Name Payload : Type) := Semantics.Arena.State (Fin limit) (Claims Name) Payload

def Cell.claims (cell : Cell Name Payload) : Claims Name := cell.name.getD {}

def Cell.kind (profile : Profile Name Payload) (cell : Cell Name Payload) : Option Kind :=
  (cell.payload.bind profile.kind).or cell.claims.kind

def Cell.Valid [DecidableEq Name] (profile : Profile Name Payload) (cell : Cell Name Payload) : Prop :=
  ∀ payload ∈ cell.payload, (∀ kind ∈ cell.claims.kind, profile.kind payload = some kind) ∧
    ∀ id ∈ cell.claims.ids, profile.accepts id payload = true

instance [DecidableEq Name] (profile : Profile Name Payload) (cell : Cell Name Payload) :
    Decidable (cell.Valid profile) := by
  unfold Cell.Valid
  infer_instance

def Compatible {Value : Type} (left right : Option Value) : Prop :=
  ∀ value ∈ left, ∀ other ∈ right, value = other

instance {Value : Type} [DecidableEq Value] (left right : Option Value) : Decidable (Compatible left right) := by
  unfold Compatible
  infer_instance

def Cell.Extends (old next : Cell Name Payload) : Prop :=
  old.claims.ids ⊆ next.claims.ids ∧
  (∀ payload ∈ old.payload, payload ∈ next.payload) ∧
  (∀ kind ∈ old.claims.kind, kind ∈ next.claims.kind)

def Cell.Agrees (profile : Profile Name Payload) (left right : Cell Name Payload) : Prop :=
  Arena.Compatible left.payload right.payload ∧ Arena.Compatible (left.kind profile) (right.kind profile)

instance [DecidableEq Payload] (profile : Profile Name Payload) (left right : Cell Name Payload) :
    Decidable (Cell.Agrees profile left right) := by
  unfold Cell.Agrees
  infer_instance

def Cell.Compatible [DecidableEq Name] (profile : Profile Name Payload) (left right : Cell Name Payload) : Prop :=
  (∃ id ∈ left.claims.ids, id ∈ right.claims.ids) → left.Agrees profile right

instance [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload) (left right : Cell Name Payload) :
    Decidable (Cell.Compatible profile left right) := by
  unfold Cell.Compatible
  infer_instance

def State.Coherent [DecidableEq Name] (profile : Profile Name Payload) (arena : State limit Name Payload) : Prop :=
  ∀ left right : Fin limit, ∀ first ∈ arena left, ∀ second ∈ arena right, Cell.Compatible profile first second

instance [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload) (arena : State limit Name Payload) :
    Decidable (State.Coherent profile arena) := by
  unfold State.Coherent
  infer_instance

def State.Valid [DecidableEq Name] (profile : Profile Name Payload) (arena : State limit Name Payload) : Prop :=
  (∀ key : Fin limit, ∀ cell ∈ arena key, Cell.Valid profile cell) ∧ arena.Coherent profile

def State.Extends (old next : State limit Name Payload) : Prop :=
  ∀ key : Fin limit, ∀ cell ∈ old key, ∃ updated ∈ next key, Cell.Extends cell updated

/-- Claims alone do not contribute to this relation. -/
def State.observed (arena : State limit Name Payload) : Naming.Relation (Id Name) Payload :=
  fun id payload => ∃ key : Fin limit, ∃ cell ∈ arena key, id ∈ (Cell.claims cell).ids ∧ payload ∈ cell.payload

def State.candidates [DecidableEq Name] (arena : State limit Name Payload) (id : Id Name) : List (Cell Name Payload) :=
  (List.finRange limit).filterMap fun key => (arena key).filter fun cell => decide (id ∈ cell.claims.ids)

inductive Read (Value : Type) where
  | unindexed | placeholder | missing | deferred | invalid | conflict | unavailable
  | found (value : Value)
  deriving DecidableEq, Repr

def Read.andThen {Value Other : Type} (result : Read Value) (convert : Value → Read Other) : Read Other :=
  match result with
  | .unindexed => .unindexed
  | .placeholder => .placeholder
  | .missing => .missing
  | .deferred => .deferred
  | .invalid => .invalid
  | .conflict => .conflict
  | .unavailable => .unavailable
  | .found value => convert value

def Read.ofOption {Value : Type} : Option Value → Read Value
  | none => .unavailable
  | some value => .found value

/-- A deterministic scan of the finite arena; aliases do not choose an
arbitrary winner. No serializer, hash or reader is invoked by this lookup. -/
def State.lookup [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (id : Id Name) (expect : Option Kind := none) : Read Payload :=
  let cells := arena.candidates id
  let payloads := cells.filterMap Semantics.Arena.Slot.payload
  if cells.isEmpty then .unindexed
  else if ∃ first ∈ cells, ∃ second ∈ cells, ¬ Cell.Agrees profile first second then .conflict
  else if ∃ cell ∈ cells, ¬ Compatible expect (Cell.kind profile cell) then .invalid
  else match payloads with
    | [] => .placeholder
    | value :: _ =>
      if expect.isSome && (profile.kind value).isNone then .invalid else .found value

def State.readWire [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (id : Id Name) (expect : Option Kind := none) : Read ByteArray :=
  (arena.lookup profile id expect).andThen (Read.ofOption ∘ profile.wire id)

def State.readGit [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (oid : Oid) (expect : Option Kind := none) : Read ByteArray :=
  arena.readWire profile (.git oid) expect

def State.readCas [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (lane : CasLane) (name : Name) : Read ByteArray :=
  arena.readWire profile (.cas lane name)

inductive Fault where
  | occupied | vacant | unclaimed | unavailable | missing | deferred | invalid | conflict
  deriving DecidableEq, Repr

inductive Edit (Name Payload : Type) where
  | insert (payload : Payload)
  | reserve (id : Id Name) (kind : Option Kind := none)
  | attach (id : Id Name) (kind : Option Kind := none)
  | materialize (payload : Payload)

def Edit.apply [DecidableEq Name] [DecidableEq Payload] :
    Edit Name Payload → Option (Cell Name Payload) → Except Fault (Cell Name Payload)
  | .insert payload, none => .ok ⟨none, some payload⟩
  | .reserve id kind, none => .ok ⟨some ⟨[id], kind⟩, none⟩
  | .insert _, some _ | .reserve _ _, some _ => .error .occupied
  | .attach id kind, some cell =>
    if Compatible cell.claims.kind kind then
      .ok { cell with name := some (cell.claims.attach id kind) }
    else .error .invalid
  | .materialize payload, some cell =>
    if Compatible cell.payload (some payload) then .ok { cell with payload := some payload }
    else .error .conflict
  | _, none => .error .vacant

/-- Revalidate the edited slot, then check alias agreement. Unchanged slots
are not rehashed. A failed edit has no post-state. -/
def State.step [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (key : Fin limit) (edit : Edit Name Payload) :
    Except Fault (State limit Name Payload) :=
  match edit.apply (arena key) with
  | .error fault => .error fault
  | .ok cell =>
    if cell.Valid profile then
      let after : State limit Name Payload := Semantics.Arena.State.replaceAt arena key (some cell)
      if after.Coherent profile then .ok after else .error .conflict
    else .error .invalid

def State.assign [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (key : Fin limit) (lane : Lane) :
    Except Fault (Id Name × State limit Name Payload) := do
  let some cell := arena key | throw .vacant
  let some payload := cell.payload | throw .unavailable
  let some id := profile.derive lane payload | throw .unavailable
  let after ← arena.step profile key (.attach id none)
  pure (id, after)

inductive Fetch (Value : Type) where
  | missing | deferred | invalid | conflict
  | found (value : Value)
  deriving DecidableEq, Repr

abbrev Reader (Name Payload : Type) := Id Name → Fetch Payload

/-- A reader is consulted only for a claimed, nonresident slot. A returned
payload must pass the same checks as direct materialization. -/
def State.cache [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (key : Fin limit) (id : Id Name) (read : Reader Name Payload) :
    Except Fault (Payload × State limit Name Payload) := do
  let some cell := arena key | throw .vacant
  if id ∉ (Cell.claims cell).ids then throw .unclaimed
  match cell.payload with
  | some payload => pure (payload, arena)
  | none => match read id with
    | .missing => throw .missing
    | .deferred => throw .deferred
    | .invalid => throw .invalid
    | .conflict => throw .conflict
    | .found payload => do
      let after ← arena.step profile key (.materialize payload)
      pure (payload, after)

/-- A codec view carries claims along unchanged; this is not an assertion
that a new payload representation binds the same names. -/
def State.codecView {Target : Type} (codec : Dasl.Arena.Codec (Claims Name) Payload Target)
    (arena : State limit Name Payload) : State limit Name Target :=
  Dasl.Arena.Converter.discard codec.encode arena

def State.codecRejects {Target : Type} (codec : Dasl.Arena.Codec (Claims Name) Payload Target)
    (arena : State limit Name Payload) (key : Fin limit) : Bool :=
  Dasl.Arena.Converter.rejected codec.encode (arena key)

end Silmaril.Formats.Git.Arena
