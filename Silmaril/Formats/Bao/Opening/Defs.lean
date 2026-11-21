module

public import Silmaril.Formats.Bao.Defs

/-! Lowering from a wire schedule to a compression-independent, possibly grouped opening. -/

@[expose] public section

namespace Silmaril.Formats.Bao

inductive Frontier where
  | opaque (expected : Digest)
  | data (span : Span) (bytes : Bytes)
  | fork (left right : Frontier)
  deriving Repr

def Frontier.edgeData : Frontier → Option (Span × Bytes)
  | .opaque _ => none
  | .data span bytes => some (span, bytes)
  | .fork _ right => right.edgeData

/-- A candidate for an EOF opening, not a checked EOF. Even the empty root must supply
its zero-width data cell; an opaque root cannot be passed to the compression kernel. -/
def Frontier.edgeAt (size : Nat) (frontier : Frontier) : Bool :=
  match frontier.edgeData with
  | none => false
  | some (span, bytes) => span.endChunk == chunks size && span.byteStart + bytes.length == size

/-- Consume a prefix of cells. A skipped/unread subtree retains the expected CV from its
parent, without asserting that the opaque CV has a preimage. `lowerPrefix` rules out
an opaque root and surplus fields. -/
def fillFrontier (expected : Digest) : Plan → List Bytes → Option (Frontier × List Bytes)
  | .skip, fields => some (.opaque expected, fields)
  | _, [] => some (.opaque expected, [])
  | .leaf span width, field :: rest =>
    if field.length = width then some (.data span field, rest) else none
  | .fork _ left right, field :: rest => do
    let (leftCV, rightCV) ← splitPair field
    let (lhs, remaining) ← fillFrontier leftCV left rest
    let (rhs, tail) ← fillFrontier rightCV right remaining
    return (.fork lhs rhs, tail)

/-- Convert an exhaustive tape or a proper prefix of whole fields to a candidate for
the kernel. In a grouped leaf keep the absolute starting chunk and all its bytes. -/
def lowerPrefix (plan : Plan) (root : Digest) (fields : List Bytes) : Option Frontier := do
  let (frontier, rest) ← fillFrontier root plan fields
  match frontier, rest with
  | .opaque _, _ => none
  | _, [] => some frontier
  | _, _ :: _ => none

/-- Reference slot/width relation for lowering, including a locally exhausted prefix. -/
inductive Fills : Digest → Plan → List Bytes → Frontier → List Bytes → Prop where
  | skip {expected : Digest} {fields : List Bytes} :
      Fills expected .skip fields (.opaque expected) fields
  | unread {expected : Digest} {plan : Plan} : Fills expected plan [] (.opaque expected) []
  | data {expected : Digest} {span : Span} {width : Nat} {bytes : Bytes} {rest : List Bytes} :
      bytes.length = width → Fills expected (.leaf span width) (bytes :: rest) (.data span bytes) rest
  | fork {expected leftCV rightCV : Digest} {span : Span} {left right : Plan}
      {pair : Bytes} {fields middle tail : List Bytes} {lhs rhs : Frontier} :
      splitPair pair = some (leftCV, rightCV) → Fills leftCV left fields lhs middle →
      Fills rightCV right middle rhs tail →
      Fills expected (.fork span left right) (pair :: fields) (.fork lhs rhs) tail

/-- Bytes confirmed by a caller-supplied kernel at the indexed *claimed* extent. -/
structure StagedRange (Range : Digest → Nat → Nat → Bytes → Prop) (digest : Digest) (claim : Nat) where
  offset : Nat
  bytes : Bytes
  checked : Range digest claim offset bytes

/-- Trusted extent must come from outside the response, or from an independent kernel
EOF certificate. The two indices prevent using a certificate for another root or claim. -/
inductive ExtentEvidence (Trusted EOF : Digest → Nat → Prop) (digest : Digest) (claim : Nat) : Prop where
  | trusted : Trusted digest claim → ExtentEvidence Trusted EOF digest claim
  | checkedEOF : EOF digest claim → ExtentEvidence Trusted EOF digest claim

def releaseRanges {Range : Digest → Nat → Nat → Bytes → Prop} {Trusted EOF : Digest → Nat → Prop}
    {digest : Digest} {claim : Nat} (permit : Option (PLift (ExtentEvidence Trusted EOF digest claim)))
    (pending : List (StagedRange Range digest claim)) : Option (List (Nat × Bytes)) :=
  permit.map fun _ => pending.map fun fragment => (fragment.offset, fragment.bytes)

end Silmaril.Formats.Bao
