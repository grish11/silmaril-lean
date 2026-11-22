module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming.NegativeCache

inductive Cause where
  | wire
  | node
  deriving DecidableEq

inductive Deferred where
  | missing
  | unavailable
  | fetchError
  | fuel
  | invalidated
  | mismatch
  deriving DecidableEq

inductive Outcome (Node : Type) where
  | found (node : Node)
  | invalid (cause : Cause)
  | deferred (why : Deferred)

/-- Pure, deterministic stages. `none` must mean definitive rejection, not
exhausted budget, a transient read failure, or failure in a dependency. -/
structure Profile (Wire Parsed Node : Type) where
  parse? : Wire → Option Parsed
  node? : Parsed → Option Node

def Profile.inspect {Wire Parsed Node : Type} (profile : Profile Wire Parsed Node) (wire : Wire) : Except Cause Node :=
  match profile.parse? wire with
  | none => .error .wire
  | some parsed => match profile.node? parsed with
    | none => .error .node
    | some node => .ok node

/-- Compatibility is not inferred from hash equality or a successful fetch. -/
structure Source {Name Wire : Type} (policy : Relation Name Wire) where
  bindings : Relation Name Wire
  bound : Binding bindings
  compatible : Subset bindings policy

variable {Name Wire Parsed Node : Type} {policy : Relation Name Wire}

/-- A successful acquisition carries membership at the requested name. An
ordinary `invalid` response without this proof is not authoritative. -/
abbrev Verified (source : Source policy) (name : Name) := {wire // source.bindings name wire}

abbrev Input (source : Source policy) (name : Name) := Except Deferred (Verified source name)

structure Rejection (source : Source policy) (profile : Profile Wire Parsed Node) (name : Name) where
  verified : Verified source name
  cause : Cause
  checked : profile.inspect verified.val = .error cause

/-- A partition for the actual profile semantics and source, not just a user
label. A profile or non-monotone source change needs a fresh partition. -/
abbrev Cache (source : Source policy) (profile : Profile Wire Parsed Node) :=
  (name : Name) → Option (Rejection source profile name)

namespace Cache

variable {source extended : Source policy} {profile : Profile Wire Parsed Node}

def empty : Cache source profile := fun _ => none

def lookup (cache : Cache source profile) (name : Name) : Option Cause := (cache name).map Rejection.cause

def insert [DecidableEq Name] (cache : Cache source profile) {name : Name}
    (rejected : Rejection source profile name) : Cache source profile :=
  fun query => if same : name = query then some (same ▸ rejected) else cache query

/-- This processes a fresh read independently of cache lookup. A transient
outcome never writes a rejection. A caller may separately use `lookup` to
avoid fetching a block that already has a proven rejection. -/
def step [DecidableEq Name] (cache : Cache source profile) (name : Name) (input : Input source name) :
    Outcome Node × Cache source profile :=
  match input with
  | .error issue => (.deferred issue, cache)
  | .ok verified => match checked : profile.inspect verified.val with
    | .ok node => (.found node, cache)
    | .error cause => (.invalid cause, cache.insert ⟨verified, cause, checked⟩)

/-- Retain exactly the certified entries under a binding, policy-compatible
extension (the two `Source`s supply those guarantees). -/
def extend (cache : Cache source profile) (included : Subset source.bindings extended.bindings) : Cache extended profile :=
  fun name => (cache name).map fun rejected =>
    ⟨⟨rejected.verified.val, included rejected.verified.property⟩, rejected.cause, rejected.checked⟩

end Cache
end Silmaril.Semantics.Naming.NegativeCache
