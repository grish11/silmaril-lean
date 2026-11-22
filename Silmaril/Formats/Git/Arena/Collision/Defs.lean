module

public import Silmaril.Formats.Git.Arena.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Arena.Collision

inductive Policy where
  | strict | retain
  deriving DecidableEq, Repr

/-- Policy dispatch is independent of the digest computation. -/
abbrev Policies := Native.Algorithm → Policy

abbrev Digest := (algorithm : Native.Algorithm) → ByteArray → Option (Native.NameBytes algorithm)

/-- `admits` is the native format boundary, not a digest test. The input to
both hooks is the exact uncompressed native preimage, including its header. -/
structure Verifier where
  admits : Native.Algorithm → ByteArray → Bool
  digest : Digest

inductive Verification where
  | verified | malformed | unavailable | mismatch
  deriving DecidableEq, Repr

def Verifier.verify (verifier : Verifier) (oid : Oid) (bytes : ByteArray) : Verification :=
  if verifier.admits oid.algorithm bytes then
    match verifier.digest oid.algorithm bytes with
    | none => .unavailable
    | some digest => if Oid.ofBytes oid.algorithm digest = oid then .verified else .mismatch
  else .malformed

inductive Input where
  | claim | missing
  | preimage (bytes : ByteArray)

inductive Outcome where
  | claimed | unverified | missing | malformed | unavailable | mismatch
  | inserted | duplicate | rejectedCollision | retainedCollision
  deriving DecidableEq, Repr

inductive Bucket where
  | empty | claim
  | verified (incumbent : ByteArray) (alternatives : List ByteArray)

def Bucket.incumbent : Bucket → Option ByteArray
  | .empty | .claim => none
  | .verified bytes _ => some bytes

def Bucket.candidates : Bucket → List ByteArray
  | .empty | .claim => []
  | .verified bytes alternatives => bytes :: alternatives

inductive Query where
  | unindexed | unverified
  | hit (bytes : ByteArray)
  | ambiguous (incumbent : ByteArray) (alternative : ByteArray) (rest : List ByteArray)
  deriving DecidableEq

def Bucket.query : Bucket → Query
  | .empty => .unindexed
  | .claim => .unverified
  | .verified bytes [] => .hit bytes
  | .verified bytes (alternative :: rest) => .ambiguous bytes alternative rest

def Bucket.admit (policy : Policy) (bucket : Bucket) (bytes : ByteArray) : Outcome × Option Bucket :=
  if bytes ∈ bucket.candidates then (.duplicate, none)
  else match bucket with
    | .empty | .claim => (.inserted, some (.verified bytes []))
    | .verified incumbent alternatives =>
      match policy with
      | .strict => (.rejectedCollision, none)
      | .retain => (.retainedCollision, some (.verified incumbent (bytes :: alternatives)))

def Bucket.edit (verifier : Verifier) (policy : Policy) (oid : Oid) (bucket : Bucket) :
    Input → Outcome × Option Bucket
  | .claim => match bucket with
    | .empty => (.claimed, some .claim)
    | _ => (.unverified, none)
  | .missing => (.missing, none)
  | .preimage bytes => match verifier.verify oid bytes with
    | .verified => bucket.admit policy bytes
    | .malformed => (.malformed, none)
    | .unavailable => (.unavailable, none)
    | .mismatch => (.mismatch, none)

abbrev Index := Oid → Bucket

def Index.empty : Index := fun _ => .empty

def Index.put (index : Index) (oid : Oid) (bucket : Bucket) : Index :=
  fun key => if key = oid then bucket else index key

def Index.query (index : Index) (oid : Oid) : Query := (index oid).query

def Index.step (verifier : Verifier) (policies : Policies) (index : Index) (oid : Oid) (input : Input) :
    Outcome × Index :=
  let (outcome, update) := (index oid).edit verifier (policies oid.algorithm) oid input
  (outcome, update.elim index (index.put oid))

def Index.Valid (verifier : Verifier) (index : Index) : Prop :=
  ∀ oid, (index oid).candidates.Nodup ∧
    ∀ bytes ∈ (index oid).candidates, verifier.verify oid bytes = .verified

def Index.Extends (before after : Index) : Prop :=
  ∀ oid, (∀ bytes ∈ (before oid).incumbent, (after oid).incumbent = some bytes) ∧
    (before oid).candidates ⊆ (after oid).candidates

abbrev Event := Oid × Input

def Index.run (verifier : Verifier) (policies : Policies) (index : Index) : List Event → List Outcome × Index
  | [] => ([], index)
  | (oid, input) :: rest =>
    let (outcome, updated) := index.step verifier policies oid input
    let (outcomes, final) := updated.run verifier policies rest
    (outcome :: outcomes, final)

/-- A verified input may confirm a previous native preimage, but not disagree
with it. Claims and failed verification do not constrain the trace. -/
def Index.Safe (verifier : Verifier) (index : Index) (oid : Oid) : Input → Prop
  | .preimage bytes => verifier.verify oid bytes = .verified →
    ∀ incumbent ∈ (index oid).incumbent, incumbent = bytes
  | _ => True

/-- Define collision freedom using the history-retaining reference run, not a
hash assumption or the absence of a rejection in some chosen policy. -/
def Index.CollisionFree (verifier : Verifier) (index : Index) : List Event → Prop
  | [] => True
  | (oid, input) :: rest => index.Safe verifier oid input ∧
    (index.step verifier (fun _ => .retain) oid input).2.CollisionFree verifier rest

/-- The dispute index and the coherent CAS arena are independent. A Git event
does not publish any new CAS binding; use the existing checked arena edits for
that. Git reads through this wrapper use the policy index, not slot claims. -/
structure Store (limit : Nat) (Name Payload : Type) where
  git : Index
  cas : Arena.State limit Name Payload

def Store.step {limit : Nat} {Name Payload : Type} (verifier : Verifier) (policies : Policies)
    (store : Store limit Name Payload) (oid : Oid) (input : Input) : Outcome × Store limit Name Payload :=
  let (outcome, git) := store.git.step verifier policies oid input
  (outcome, { store with git })

def Store.readRaw {Name Payload : Type} [DecidableEq Name] [DecidableEq Payload] {limit : Nat}
    (profile : Arena.Profile Name Payload) (store : Store limit Name Payload) (name : Name) : Read ByteArray :=
  store.cas.readCas profile .raw name

def Outcome.isCollision : Outcome → Bool
  | .rejectedCollision | .retainedCollision => true
  | _ => false

/-- A fail-closed consumer can latch collision notices outside the committed
store. A strict rejection changes no store state but still emits a notice. -/
abbrev Disputes := Oid → Bool

def Disputes.record (blocked : Disputes) (oid : Oid) (outcome : Outcome) : Disputes :=
  fun key => blocked key || (key == oid && outcome.isCollision)

/-- `blocked` is the current external dispute/trust view. Both endpoints must
encode to the observed preimage; semantic equality separately requires recovery.
The proposition is snapshot-local: consumers revalidate it before seeding a
live equality view. -/
def Index.Seed {Value : Type} (index : Index) (blocked : Oid → Bool)
    (encode : Value → Option ByteArray) (oid : Oid) (left right : Value) : Prop :=
  blocked oid = false ∧ ∃ bytes, index.query oid = .hit bytes ∧
    encode left = some bytes ∧ encode right = some bytes

def Index.canSeed {Value : Type} (index : Index) (blocked : Disputes)
    (encode : Value → Option ByteArray) (oid : Oid) (left right : Value) : Bool :=
  !blocked oid && (match index.query oid with
    | .hit bytes => decide (encode left = some bytes ∧ encode right = some bytes)
    | _ => false)

end Silmaril.Formats.Git.Arena.Collision
