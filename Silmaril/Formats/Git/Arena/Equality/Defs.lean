module

public import Silmaril.Formats.Git.Arena.Collision.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Arena.Equality

open Silmaril.Formats.Dasl.Encode (PartialCodec)

/-- Optional external authority. The premise is functionality of its explicit
validation relation for a fixed OID and observed preimage, not of SHA-256. -/
structure Sha256Authority (Payload : Type) where
  accepts : Native.NameBytes .sha256 → ByteArray → Payload → Bool
  binds : ∀ ⦃oid bytes left right⦄, accepts oid bytes left = true → accepts oid bytes right = true → left = right

structure Snapshot (limit : Nat) (Name Payload : Type) where
  arena : Arena.State limit Name Payload
  profile : Arena.Profile Name Payload
  nativeCodec : Native.Algorithm → PartialCodec Payload ByteArray
  git : Collision.Index
  blocked : Collision.Disputes
  authority : Option (Sha256Authority Payload)

inductive Evidence (Name : Type) where
  | content
  | canonicalCas (lane : CasLane) (name : Name)
  | nativeBytes (oid : Oid)
  | trustedGit (oid : Oid)

def Evidence.oid? {Name : Type} : Evidence Name → Option Oid
  | .nativeBytes oid | .trustedGit oid => some oid
  | _ => none

structure Request (limit : Nat) (Name : Type) where
  left : Fin limit
  right : Fin limit
  evidence : Evidence Name

inductive Reject where
  | nonresident | differentCas (lane : CasLane) | contentMismatch | casUnbound
  | oidBlocked | nativeEvidence | trustUnavailable | nonuniqueOid | untrusted
  deriving DecidableEq, Repr

variable {Name Payload Value : Type} {limit : Nat}

def Snapshot.payloadAt (snapshot : Snapshot limit Name Payload) (key : Fin limit) : Option Payload :=
  (snapshot.arena key).bind Silmaril.Semantics.Arena.Slot.payload

def Snapshot.claimsAt (snapshot : Snapshot limit Name Payload) (key : Fin limit) : List (Arena.Id Name) :=
  ((snapshot.arena key).map fun cell => (Cell.claims cell).ids).getD []

/-- Content-only observation, never a transfer of identifier claims to another slot. -/
def Snapshot.typedAt (snapshot : Snapshot limit Name Payload) (codec : PartialCodec Value ByteArray)
    (encode : Payload → Option ByteArray) (key : Fin limit) : Option Value :=
  (snapshot.payloadAt key).bind fun payload => (encode payload).bind codec.decode?

def Snapshot.readRaw [DecidableEq Name] [DecidableEq Payload] (snapshot : Snapshot limit Name Payload)
    (name : Name) : Arena.Read ByteArray := snapshot.arena.readCas snapshot.profile .raw name

def Snapshot.deliver (snapshot : Snapshot limit Name Payload) (oid : Oid) (outcome : Collision.Outcome) :
    Snapshot limit Name Payload := { snapshot with blocked := snapshot.blocked.record oid outcome }

/-- Disable OID evidence independently of collision detection, e.g. when
an authority or its provenance has been revoked. -/
def Snapshot.revoke (snapshot : Snapshot limit Name Payload) (oid : Oid) : Snapshot limit Name Payload :=
  { snapshot with blocked := fun key => decide (key = oid) || snapshot.blocked key }

/-- Compare two actual derivations under the same profile and lane. This
ignores all user-asserted CAS labels. -/
def Snapshot.casDifferent [DecidableEq Name] (snapshot : Snapshot limit Name Payload) (lane : CasLane)
    (left right : Payload) : Bool :=
  match snapshot.profile.derive (.cas lane) left, snapshot.profile.derive (.cas lane) right with
  | some first, some second => decide (first ≠ second)
  | _, _ => false

def Snapshot.checkEvidence [DecidableEq Name] [DecidableEq Payload] (snapshot : Snapshot limit Name Payload)
    (request : Request limit Name) (left right : Payload) : Except Reject Unit :=
  match request.evidence with
  | .content => if left = right then .ok () else .error .contentMismatch
  | .canonicalCas lane name =>
    let id : Arena.Id Name := .cas lane name
    if id ∈ snapshot.claimsAt request.left ∧ id ∈ snapshot.claimsAt request.right ∧
        snapshot.profile.derive (.cas lane) left = some id ∧ snapshot.profile.derive (.cas lane) right = some id then
      .ok ()
    else .error .casUnbound
  | .nativeBytes oid =>
    if snapshot.git.canSeed snapshot.blocked (snapshot.nativeCodec oid.algorithm).encode? oid left right then
      .ok ()
    else .error .nativeEvidence
  | .trustedGit (.sha1 _) => .error .trustUnavailable
  | .trustedGit (.sha256 digest) =>
    match snapshot.authority with
    | none => .error .trustUnavailable
    | some authority =>
      match snapshot.git.query (.sha256 digest) with
      | .hit bytes => if authority.accepts digest bytes left && authority.accepts digest bytes right then
          .ok () else .error .untrusted
      | _ => .error .nonuniqueOid

/-- Check the current dispute view before using any OID-based request. CAS
disequality is checked before considering the requested evidence. -/
def Snapshot.check [DecidableEq Name] [DecidableEq Payload] (snapshot : Snapshot limit Name Payload)
    (request : Request limit Name) : Except Reject Unit :=
  if request.evidence.oid?.any snapshot.blocked then .error .oidBlocked
  else match snapshot.payloadAt request.left, snapshot.payloadAt request.right with
    | some left, some right =>
      if snapshot.casDifferent .raw left right then .error (.differentCas .raw)
      else if snapshot.casDifferent .object left right then .error (.differentCas .object)
      else snapshot.checkEvidence request left right
    | _, _ => .error .nonresident

/-- Live replay takes the original requests, not a previously merged graph.
Keep the evidence tag on each edge so that it can be rechecked. -/
def Snapshot.replay [DecidableEq Name] [DecidableEq Payload] (snapshot : Snapshot limit Name Payload)
    (requests : List (Request limit Name)) : List (Request limit Name) :=
  requests.filter fun request => (snapshot.check request).isOk

/-- Undirected equality closure of admitted edges. This is a specification
for a checked replay or a future union-find, not congruence on arbitrary ASTs. -/
inductive Related (edges : List (Request limit Name)) : Fin limit → Fin limit → Prop where
  | refl (key : Fin limit) : Related edges key key
  | edge {request : Request limit Name} (member : request ∈ edges) : Related edges request.left request.right
  | symm {left right : Fin limit} : Related edges left right → Related edges right left
  | trans {left middle right : Fin limit} : Related edges left middle → Related edges middle right → Related edges left right

end Silmaril.Formats.Git.Arena.Equality
