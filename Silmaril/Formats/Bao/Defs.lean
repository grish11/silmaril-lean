module

public import Init

/-! Official Bao framing, with a small interface for an unkeyed BLAKE3 verifier. -/

@[expose] public section

namespace Silmaril.Formats.Bao

abbrev Bytes := List UInt8
abbrev Digest := Vector UInt8 32

def chunkBytes : Nat := 1024
def u64Limit : Nat := 2^64

def putLE : Nat → Nat → Bytes
  | 0, _ => []
  | width + 1, size => UInt8.ofNat size :: putLE width (size / 256)

def putLE64 (size : Nat) : Bytes := putLE 8 size

def getLE : Bytes → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * getLE rest

def takeExact (width : Nat) (input : Bytes) : Option (Bytes × Bytes) :=
  let field := input.take width
  if field.length = width then some (field, input.drop width) else none

def readHeader (input : Bytes) : Option (Nat × Bytes) := do
  let (header, rest) ← takeExact 8 input
  return (getLE header, rest)

/-- The empty blob still has one (zero-byte) leaf. -/
def chunks (size : Nat) : Nat := max 1 ((size + chunkBytes - 1) / chunkBytes)

structure Span where
  first : Nat
  count : Nat
  deriving BEq, DecidableEq, Repr

def Span.endChunk (span : Span) : Nat := span.first + span.count
def Span.byteStart (span : Span) : Nat := span.first * chunkBytes
def Span.byteSize (size : Nat) (span : Span) : Nat :=
  min size (span.endChunk * chunkBytes) - span.byteStart

/-- Largest power of two strictly below `count` for a non-leaf. -/
def Span.split (span : Span) : Span × Span :=
  let midpoint := 2 ^ (span.count - 1).log2
  (⟨span.first, midpoint⟩, ⟨span.first + midpoint, span.count - midpoint⟩)

theorem Span.split_decreases (span : Span) (nontrivial : 1 < span.count) :
    0 < span.split.1.count ∧ span.split.1.count < span.count ∧
    span.split.2.count < span.count := by
  have below := ((Nat.log2_eq_iff (n := span.count - 1) (by omega)).mp rfl).1
  have positive : 0 < 2 ^ (span.count - 1).log2 := Nat.two_pow_pos _
  simp only [Span.split]
  omega

structure Interval where
  start : Nat
  stop : Nat
  deriving BEq, DecidableEq, Repr

def Selected (query : List Interval) (index : Nat) : Prop :=
  ∃ range ∈ query, range.start ≤ index ∧ index < range.stop

def Contains (span : Span) (index : Nat) : Prop := span.first ≤ index ∧ index < span.endChunk

def overlaps (query : List Interval) (span : Span) : Bool :=
  query.any fun range => range.start < span.endChunk && span.first < range.stop

/-- Coverage by a list ordered by start; adjacent intervals need not be merged. -/
def covers (query : List Interval) (span : Span) : Bool :=
  let endCovered := query.foldl (fun cursor range =>
    if range.start ≤ cursor then max cursor range.stop else cursor) span.first
  span.endChunk ≤ endCovered

inductive Plan where
  | skip
  | leaf (span : Span) (width : Nat)
  | fork (span : Span) (left right : Plan)
  deriving Repr

/-- Build only the selected paths. `group` bounds elision of fully selected subtrees;
an intersecting partial group is expanded, down to 1 KiB chunks if needed. -/
def planAt (size group : Nat) (query : List Interval) (span : Span) : Plan :=
  if !overlaps query span then .skip
  else if _small : span.count ≤ 1 then .leaf span (span.byteSize size)
  else if span.count ≤ group && covers query span then .leaf span (span.byteSize size)
  else .fork span (planAt size group query span.split.1) (planAt size group query span.split.2)
termination_by span.count
decreasing_by
  · exact (span.split_decreases (by omega)).2.1
  · exact (span.split_decreases (by omega)).2.2

def plan (size group : Nat) (query : List Interval) : Plan :=
  planAt size group query ⟨0, chunks size⟩

def fullPlan (size group : Nat) : Plan := plan size group [⟨0, chunks size⟩]

inductive Slot where
  | pair (span : Span)
  | data (span : Span) (width : Nat)
  deriving BEq, DecidableEq, Repr

def Slot.width : Slot → Nat
  | .pair _ => 64
  | .data _ width => width

def Plan.preorder : Plan → List Slot
  | .skip => []
  | .leaf span width => [.data span width]
  | .fork span left right => .pair span :: (left.preorder ++ right.preorder)

def Plan.pairs (postorder : Bool) : Plan → List Slot
  | .skip | .leaf .. => []
  | .fork span left right =>
    let children := left.pairs postorder ++ right.pairs postorder
    if postorder then children ++ [.pair span] else .pair span :: children

/-- The reference tape relation, in slot order. No tags or per-field lengths are on wire. -/
def Tape : List Slot → List Bytes → Prop
  | [], [] => True
  | slot :: slots, field :: fields => field.length = slot.width ∧ Tape slots fields
  | _, _ => False

def readSlots : List Slot → Bytes → Option (List Bytes × Bytes)
  | [], input => some ([], input)
  | slot :: slots, input => do
    let (field, rest) ← takeExact slot.width input
    let (fields, tail) ← readSlots slots rest
    return (field :: fields, tail)

def readFrame (layout : List Slot) (input : Bytes) : Option (List Bytes) := do
  let (fields, rest) ← readSlots layout input
  if rest.isEmpty then some fields else none

/-- Attach coordinate/type tags off wire. This list can be used as a detached event tape. -/
def positioned (layout : List Slot) (fields : List Bytes) : List (Slot × Bytes) :=
  layout.zip fields

/-- A detached proof indexed by the exact coordinate/width schedule. It carries no
root or length assertion; it is admissible input to a verifier, not verified output. -/
inductive Detached : List Slot → Type where
  | nil : Detached []
  | cons (slot : Slot) {tail : List Slot} (field : Vector UInt8 slot.width)
      (rest : Detached tail) : Detached (slot :: tail)

def detach : (layout : List Slot) → List Bytes → Option (Detached layout)
  | [], [] => some .nil
  | slot :: layout, field :: fields => do
    if h : field.length = slot.width then
      return .cons slot ⟨field.toArray, by simpa using h⟩ (← detach layout fields)
    else none
  | _, _ => none

def Detached.fields {layout : List Slot} : Detached layout → List Bytes
  | .nil => []
  | .cons _ field rest => field.toArray.toList :: rest.fields

def writeSlots (source : Slot → Option Bytes) (layout : List Slot) : Option Bytes := do
  let fields ← layout.mapM fun slot => do
    let field ← source slot
    if field.length = slot.width then some field else none
  return fields.flatten

structure RangeRequest where
  start : Nat
  count : Nat
  deriving Repr

def RangeRequest.valid (request : RangeRequest) : Bool :=
  request.start < u64Limit && request.count < u64Limit

/-- Bao's permissive selection. Use Nat for start+count, never wrapping arithmetic.
Count zero still supplies evidence for one chunk; starts at/past EOF select the last chunk. -/
def sliceChunks (size : Nat) (request : RangeRequest) : Interval :=
  let last := chunks size - 1
  ⟨min last (request.start / chunkBytes),
    1 + min last ((request.start + max 1 request.count - 1) / chunkBytes)⟩

def slicePlan (size : Nat) (request : RangeRequest) : Plan :=
  plan size 1 [sliceChunks size request]

/-- Visible byte window (different from proof coverage). Its endpoint is not an EOF witness. -/
def sliceWindow (size : Nat) (request : RangeRequest) : Interval :=
  ⟨min size request.start, min size (request.start + request.count)⟩

def strictBounds (size : Nat) (request : RangeRequest) : Bool :=
  request.start ≤ size && request.count ≤ size - request.start

inductive Encoding where
  | combined
  | outboard
  | slice (request : RangeRequest)
  deriving Repr

def Encoding.layout (encoding : Encoding) (size : Nat) : List Slot :=
  match encoding with
  | .combined => (fullPlan size 1).preorder
  | .outboard => (fullPlan size 1).pairs false
  | .slice request => (slicePlan size request).preorder

def Encoding.valid : Encoding → Bool
  | .slice request => request.valid
  | _ => true

/-- A cheap rejection before building a plan for an adversarial large header. For a slice
the selected chunk bytes alone are a lower bound for the body size. -/
def Encoding.bodyFits (encoding : Encoding) (size available : Nat) : Bool :=
  let pairs := 64 * (chunks size - 1)
  match encoding with
  | .combined => pairs + size ≤ available
  | .outboard => pairs ≤ available
  | .slice request =>
    let window := sliceChunks size request
    min size (window.stop * chunkBytes) - window.start * chunkBytes ≤ available

def encode (encoding : Encoding) (size : Nat) (source : Slot → Option Bytes) : Option Bytes := do
  if !(size < u64Limit && encoding.valid) then none else
    let body ← writeSlots source (encoding.layout size)
    return putLE64 size ++ body

/-- Strict single-frame decoding; a slice uses the caller's request, not bytes in the frame.
For outboards, `fields` contains pairs only and the original data is a separate input. -/
def decode (encoding : Encoding) (input : Bytes) : Option (Nat × List Bytes) := do
  if !encoding.valid then none else
    let (size, body) ← readHeader input
    if !encoding.bodyFits size body.length then none else
      let fields ← readFrame (encoding.layout size) body
      return (size, fields)

/-- Reinterleave pairs and original data, or select a slice, by a coordinate lookup.
The original data must have exactly the claimed length; this is framing, not authentication. -/
def outboardSource (pairs : List (Slot × Bytes)) (original : Bytes)
    (slot : Slot) : Option Bytes :=
  match slot with
  | .pair _ => (pairs.find? fun entry => entry.1 == slot).map Prod.snd
  | .data span width => (takeExact width (original.drop span.byteStart)).map Prod.fst

def fromOutboard (target : Encoding) (encoded original : Bytes) : Option Bytes := do
  let (size, fields) ← decode .outboard encoded
  if original.length != size then none else
    encode target size (outboardSource (positioned (Encoding.outboard.layout size) fields) original)

def fromCombined (target : Encoding) (combined : Bytes) : Option Bytes := do
  let (size, fields) ← decode .combined combined
  let tape := positioned (Encoding.combined.layout size) fields
  encode target size fun slot => (tape.find? fun entry => entry.1 == slot).map Prod.snd

/-- Both callbacks must distinguish root output from a non-root chaining value. The
leaf callback hashes the entire subtree at its absolute BLAKE3 chunk counter. -/
structure HashOps where
  parent : (root : Bool) → Digest → Digest → Digest
  subtree : (root : Bool) → (startChunk : Nat) → Bytes → Digest

inductive Event where
  | parent (span : Span) (left right : Digest)
  | data (span : Span) (bytes : Bytes)
  deriving Repr

/-- An expected digest is reachable from a trusted root via checked parent pairs at
the claimed geometry. This is not a statement about a reference of unknown extent. -/
inductive AuthPath (hash : HashOps) (tree : Plan) (digest : Digest) :
    Plan → Digest → Bool → Prop where
  | root : AuthPath hash tree digest tree digest true
  | left {span : Span} {left right : Plan} {root : Bool} {lcv rcv : Digest} :
      AuthPath hash tree digest (.fork span left right) (hash.parent root lcv rcv) root →
      AuthPath hash tree digest left lcv false
  | right {span : Span} {left right : Plan} {root : Bool} {lcv rcv : Digest} :
      AuthPath hash tree digest (.fork span left right) (hash.parent root lcv rcv) root →
      AuthPath hash tree digest right rcv false

inductive Checked (hash : HashOps) (tree : Plan) (digest : Digest) : Event → Prop where
  | parent {span : Span} {left right : Plan} {root : Bool} {lcv rcv : Digest} :
      AuthPath hash tree digest (.fork span left right) (hash.parent root lcv rcv) root →
      Checked hash tree digest (.parent span lcv rcv)
  | data {span : Span} {bytes : Bytes} {root : Bool} :
      AuthPath hash tree digest (.leaf span bytes.length)
      (hash.subtree root span.first bytes) root → Checked hash tree digest (.data span bytes)

def EdgeEvent (size : Nat) : Event → Prop
  | .data span bytes => span.endChunk = chunks size ∧ span.byteStart + bytes.length = size
  | .parent .. => False

structure Work where
  node : Plan
  expected : Digest
  root : Bool

def enqueue (node : Plan) (expected : Digest) (root : Bool) (tail : List Work) : List Work :=
  match node with
  | .skip => tail
  | _ => ⟨node, expected, root⟩ :: tail

structure Session where
  pending : List Work
  rightEdge : Bool := false

def Rooted (hash : HashOps) (tree : Plan) (digest : Digest) (state : Session) : Prop :=
  ∀ work ∈ state.pending, AuthPath hash tree digest work.node work.expected work.root

def start (tree : Plan) (root : Digest) : Session := ⟨enqueue tree root true [], false⟩

def digest? (bytes : Bytes) : Option Digest :=
  if h : bytes.length = 32 then
    some ⟨bytes.toArray, by simpa using h⟩
  else none

def splitPair (bytes : Bytes) : Option (Digest × Digest) := do
  let left ← digest? (bytes.take 32)
  let right ← digest? (bytes.drop 32)
  return (left, right)

/-- Consume one complete cell. The observations are internal candidates checked at the
claimed geometry; neither a caller-visible range nor the real EOF is asserted here. -/
def step (hash : HashOps) (size : Nat) (state : Session) (bytes : Bytes) :
    Option (Session × Event) :=
  match state.pending with
  | ⟨.fork span left right, expected, root⟩ :: tail => do
    let (leftCV, rightCV) ← splitPair bytes
    if hash.parent root leftCV rightCV != expected then none else
      let pending := enqueue left leftCV false (enqueue right rightCV false tail)
      return (⟨pending, state.rightEdge⟩, .parent span leftCV rightCV)
  | ⟨.leaf span width, expected, root⟩ :: tail =>
    if bytes.length == width && hash.subtree root span.first bytes == expected then
      some (⟨tail, state.rightEdge ||
        (span.endChunk == chunks size && span.byteStart + width == size)⟩, .data span bytes)
    else none
  | _ => none

/-- End of a strict standalone frame, distinct from any earlier release and from length
authentication. An enclosing stream must supply the correct frame boundary. -/
def finished (state : Session) (remainder : Bytes) (endOfFrame : Bool) : Bool :=
  state.pending.isEmpty && remainder.isEmpty && endOfFrame

/-- An edge candidate at the claimed geometry. Converting it to trusted length needs a
canonical kernel EOF proof tied to this digest; the flag alone is not such a proof. -/
def rightEdgeClaim (size : Nat) (state : Session) : Option Nat :=
  if state.rightEdge then some size else none

def nextSlot (state : Session) : Option Slot :=
  match state.pending with
  | ⟨.fork span .., _, _⟩ :: _ => some (.pair span)
  | ⟨.leaf span width, _, _⟩ :: _ => some (.data span width)
  | _ => none

def readStep (hash : HashOps) (size : Nat) (state : Session) (input : Bytes) :
    Option (Session × Event × Bytes) := do
  let slot ← nextSlot state
  let (field, rest) ← takeExact slot.width input
  let (next, event) ← step hash size state field
  return (next, event, rest)

def runSteps (hash : HashOps) (size : Nat) (state : Session) :
    List Bytes → Option (List Event × Session)
  | [] => some ([], state)
  | bytes :: fields => do
    let (next, event) ← step hash size state bytes
    let (events, final) ← runSteps hash size next fields
    return (event :: events, final)

/-- Exact framing and callbacks checked at the claimed geometry. The optional size is
an edge candidate, not evidence of a reference extent. -/
def verifyFrame (hash : HashOps) (size : Nat) (tree : Plan) (root : Digest) (body : Bytes) :
    Option (List Event × Option Nat) := do
  let fields ← readFrame tree.preorder body
  let (events, state) ← runSteps hash size (start tree root) fields
  if !finished state [] true then none else return (events, rightEdgeClaim size state)

/-- The data projected by a byte request, without using its claimed total length.
Returning an empty sublist here says nothing about authenticated EOF. -/
def requestedBytes (request : RangeRequest) : Event → Bytes
  | .parent .. => []
  | .data span bytes =>
    let start := request.start - span.byteStart
    let stop := request.start + request.count - span.byteStart
    (bytes.drop start).take (stop - start)

/-- A k-step successful prefix. The wire may still truncate or fail after this prefix. -/
inductive Steps (hash : HashOps) (size : Nat) :
    Session → List Bytes → List Event → Session → Prop where
  | nil {state : Session} : Steps hash size state [] [] state
  | cons {state next final : Session} {bytes : Bytes} {fields : List Bytes}
      {event : Event} {events : List Event} : step hash size state bytes = some (next, event) →
      Steps hash size next fields events final →
      Steps hash size state (bytes :: fields) (event :: events) final

end Silmaril.Formats.Bao
