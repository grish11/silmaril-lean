module

public import Silmaril.Formats.Git.Arena.Thms
public import Silmaril.Formats.Git.Translate.Graph.Thms

@[expose] public section

namespace Silmaril.Formats.Git.Arena

variable {Name Payload Key Target Meta : Type} {limit : Nat} {algorithm : Native.Algorithm}

def State.AllowsFetch [DecidableEq Name] (profile : Profile Name Payload) (arena : State limit Name Payload)
    (id : Id Name) (expect : Option Kind) (payload : Payload) : Prop :=
  profile.accepts id payload = true ∧
    (∀ kind ∈ expect, profile.kind payload = some kind) ∧
    ∀ cell ∈ arena.candidates id, ∀ kind ∈ Cell.kind profile cell, profile.kind payload = some kind

instance [DecidableEq Name] (profile : Profile Name Payload) (arena : State limit Name Payload)
    (id : Id Name) (expect : Option Kind) (payload : Payload) : Decidable (arena.AllowsFetch profile id expect payload) := by
  unfold State.AllowsFetch
  infer_instance

/-- Read through an indexed placeholder, without changing the snapshot.
Unknown names, conflicts and invalid requests never trigger a fetch. Only the
queried ID and its known kinds are checked; publication uses `State.cache`,
which also checks every additional claim on the updated slot. -/
def State.resolve [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (reader : Reader Name Payload) (id : Id Name) (expect : Option Kind) : Read Payload :=
  match arena.lookup profile id expect with
  | .placeholder => match reader id with
    | .missing => .missing
    | .deferred => .deferred
    | .invalid => .invalid
    | .conflict => .conflict
    | .found payload => if arena.AllowsFetch profile id expect payload then .found payload else .invalid
  | other => other

def State.Origin [DecidableEq Name] [DecidableEq Payload] (profile : Profile Name Payload)
    (arena : State limit Name Payload) (reader : Reader Name Payload) (id : Id Name) (expect : Option Kind)
    (payload : Payload) : Prop :=
  arena.observed id payload ∨ (arena.lookup profile id expect = .placeholder ∧ reader id = .found payload ∧
    arena.AllowsFetch profile id expect payload)

/-- A single Git object's decoder is separate from both the name index and
the encoding profile. One traversal uses one native algorithm throughout. -/
structure GitBackend (algorithm : Native.Algorithm) (limit : Nat) (Name Payload Key : Type) where
  profile : Profile Name Payload
  state : State limit Name Payload
  reader : Reader Name Payload
  node : (kind : Kind) → Payload → Option (Translate.Graph.Node Key (Native.NameBytes algorithm) kind)

namespace GitBackend

abbrev Source (algorithm : Native.Algorithm) := Native.NameBytes algorithm

def id (algorithm : Native.Algorithm) (oid : Source algorithm) : Id Name := .git (Oid.ofBytes algorithm oid)

variable [DecidableEq Name] [DecidableEq Payload]

def inspect (backend : GitBackend algorithm limit Name Payload Key) (kind : Kind) (oid : Source algorithm) :
    Read (Translate.Graph.Binding Key (Source algorithm) kind) :=
  (backend.state.resolve backend.profile backend.reader (id algorithm oid) (some kind)).andThen fun payload =>
    Read.ofOption (do
      let node ← backend.node kind payload
      let bytes ← backend.profile.gitBytes algorithm payload
      return ⟨node, bytes⟩)

def lookup (backend : GitBackend algorithm limit Name Payload Key) : Translate.Graph.Lookup Key (Source algorithm) :=
  fun kind oid => match backend.inspect kind oid with
    | .found binding => .found binding
    | .invalid | .conflict => .invalid
    | _ => .missing

inductive Boundary where
  | unindexed | placeholder | missing | deferred | invalid | conflict | unavailable
  deriving DecidableEq, Repr

def diagnosis {Value : Type} : Read Value → Option Boundary
  | .unindexed => some .unindexed
  | .placeholder => some .placeholder
  | .missing => some .missing
  | .deferred => some .deferred
  | .invalid => some .invalid
  | .conflict => some .conflict
  | .unavailable => some .unavailable
  | .found _ => none

inductive Fault (algorithm : Native.Algorithm) where
  | boundary (address : Translate.Graph.Address (Source algorithm)) (reason : Boundary)
  | graph (original : Translate.Graph.Error (Source algorithm))
  deriving DecidableEq

/-- Recover the precise arena diagnostic lost by the generic graph reader.
If a found binding failed the graph's own preimage/name validation, retain
that graph error. The reader denotes a fixed snapshot for the whole run. -/
def refineFault (backend : GitBackend algorithm limit Name Payload Key) :
    Translate.Graph.Error (Source algorithm) → Fault algorithm
  | error@(.missing address) | error@(.invalid address) =>
    match diagnosis (backend.inspect address.1 address.2) with
    | some reason => .boundary address reason
    | none => .graph error
  | error => .graph error

def discover [LinearOrder Key] (backend : GitBackend algorithm limit Name Payload Key)
    (profile : Translate.Profile algorithm Key (Source algorithm) Target Meta) (fuel : Nat)
    (kind : Kind) (oid : Source algorithm) :
    Except (Fault algorithm) (Translate.Graph.Plan profile.native backend.lookup (.local (kind := kind)) oid ×
      Translate.Graph.Memo profile.native backend.lookup) :=
  (Translate.Graph.discover profile backend.lookup fuel kind oid).mapError backend.refineFault

def run [LinearOrder Key] [DecidableEq Target] (backend : GitBackend algorithm limit Name Payload Key)
    (profile : Translate.Profile algorithm Key (Source algorithm) Target Meta) (fuel : Nat)
    (kind : Kind) (oid : Source algorithm) :
    Except (Fault algorithm) (Translate.Graph.Outcome profile backend.lookup kind oid) :=
  (Translate.Graph.run profile backend.lookup fuel kind oid).mapError backend.refineFault

end GitBackend
end Silmaril.Formats.Git.Arena
