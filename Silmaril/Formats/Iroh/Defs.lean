module

public import Silmaril.Formats.Bao.Defs

/-! The unkeyed raw Get and portable bao-tree 0.17.0 profile of iroh-blobs. -/

@[expose] public section

namespace Silmaril.Formats.Iroh

open Bao (Bytes Interval Slot Plan takeExact readSlots readFrame writeSlots u64Limit)

/-- A raw BLAKE3 object identifier, not a non-root chaining value. -/
structure Hash where
  bytes : Bao.Digest
  deriving DecidableEq, Repr

def groupChunks : Nat := 16
def groupBytes : Nat := groupChunks * Bao.chunkBytes
def groups (size : Nat) : Nat := max 1 ((size + groupBytes - 1) / groupBytes)
def outboardSize (size : Nat) : Nat := 64 * (groups size - 1)

/-- Alternating start/end boundaries in BLAKE3 chunks. An unmatched start is open. -/
abbrev Boundaries := List Nat

/-- Round a nonempty half-open byte range outwards to BLAKE3 chunks, not to groups. -/
def byteRange (start stop : Nat) : Option Boundaries :=
  if start > stop || stop ≥ u64Limit then none
  else if start == stop then some []
  else some [start / Bao.chunkBytes, (stop + Bao.chunkBytes - 1) / Bao.chunkBytes]

/-- `ChunkRangesExt::last_chunk`: an open range at the maximum u64 chunk index. -/
def endProbe : Boundaries := [u64Limit - 1]

def boundaries : Nat → List Nat → Option Boundaries
  | _, [] => some []
  | base, delta :: deltas => do
    let next := base + delta
    if next ≥ u64Limit then none else
      if deltas.head? == some 0 then none else
        return next :: (← boundaries next deltas)

def intervals (ceiling : Nat) : Boundaries → List Interval
  | [] => []
  | [start] => [⟨start, ceiling⟩]
  | start :: stop :: rest => ⟨start, stop⟩ :: intervals ceiling rest

def mergeClipped : List Interval → List Interval
  | [] => []
  | range :: rest =>
    match mergeClipped rest with
    | [] => [range]
    | next :: tail =>
      if next.start ≤ range.stop then ⟨range.start, max range.stop next.stop⟩ :: tail
      else range :: next :: tail

/-- Effective coverage on the actual tree. Out-of-bounds *selected chunks* map to the
last chunk, not to an empty response. The empty blob uses virtual chunk zero. -/
def clip (size : Nat) (query : Boundaries) : List Interval :=
  let count := Bao.chunks size
  mergeClipped ((intervals u64Limit query).map fun range =>
    ⟨min range.start (count - 1), min range.stop count⟩)

def responsePlan (size : Nat) (query : Boundaries) : Plan :=
  Bao.plan size groupChunks (clip size query)

def coverageBytes (size : Nat) (query : Boundaries) : Nat :=
  ((clip size query).map fun range =>
    min size (range.stop * Bao.chunkBytes) - range.start * Bao.chunkBytes).sum

/-- The 8-byte length in a response is initially only a claim. Blob frames concatenate
without a separator; the proof schedule delimits each body. -/
def readResponse (query : Boundaries) (input : Bytes) : Option (Nat × List Bytes × Bytes) := do
  let (size, body) ← Bao.readHeader input
  if coverageBytes size query > body.length then none else
    let (fields, rest) ← readSlots (responsePlan size query).preorder body
    return (size, fields, rest)

def writeResponse (size : Nat) (query : Boundaries) (source : Slot → Option Bytes) : Option Bytes := do
  if size ≥ u64Limit then none else
    let body ← writeSlots source (responsePlan size query).preorder
    return Bao.putLE64 size ++ body

/-- Start with only a header. A caller-chosen budget bounds plan allocation before any
body bytes arrive. The budget is local policy, not a property of the wire format. -/
def beginResponse (hash : Hash) (query : Boundaries) (maxCoverageBytes : Nat) (input : Bytes) :
    Option (Nat × Bao.Session × Bytes) := do
  let (size, body) ← Bao.readHeader input
  if coverageBytes size query > maxCoverageBytes then none else
    return (size, Bao.start (responsePlan size query) hash.bytes, body)

inductive Order where
  | pre
  | post
  deriving DecidableEq, Repr

def Order.postorder : Order → Bool
  | .pre => false
  | .post => true

def outboardLayout (order : Order) (size : Nat) : List Slot :=
  (Bao.fullPlan size groupChunks).pairs order.postorder

/-- Portable memory representation. The size, profile and expected root are external
to the pair bytes. No filesystem metadata or partial-store records are modeled. -/
structure Outboard where
  root : Hash
  size : Nat
  order : Order
  fields : List Bytes
  deriving Repr

def readMemory (root : Hash) (size : Nat) (order : Order) (body : Bytes) : Option Outboard := do
  if size ≥ u64Limit || body.length != outboardSize size then none else
    let fields ← readFrame (outboardLayout order size) body
    return ⟨root, size, order, fields⟩

def readTrailer (input : Bytes) : Option (Nat × Bytes) := do
  let (header, body) ← takeExact 8 input.reverse
  return (Bao.getLE header.reverse, body.reverse)

def readPortable (root : Hash) (order : Order) (input : Bytes) : Option Outboard := do
  let (size, body) ← match order with
    | .pre => Bao.readHeader input
    | .post => readTrailer input
  readMemory root size order body

def writePortable (outboard : Outboard) : Bytes :=
  let header := Bao.putLE64 outboard.size
  let body := outboard.fields.flatten
  match outboard.order with
  | .pre => header ++ body
  | .post => body ++ header

/-- Reorder by tree coordinates without rehashing. Expand a partial response group using
original data and the future compression kernel, not by inventing missing outboard pairs. -/
def reorder (order : Order) (outboard : Outboard) : Option Outboard := do
  let source := Bao.positioned (outboardLayout outboard.order outboard.size) outboard.fields
  let target := outboardLayout order outboard.size
  let body ← writeSlots (fun slot => (source.find? (fun entry => entry.1 == slot)).map Prod.snd) target
  readMemory outboard.root outboard.size order body

/-- Project a framed official Bao outboard to the portable Iroh profile. This is a
coordinate conversion only; `root` and all decoded pairs remain to be verified. -/
def fromBaoOutboard (root : Hash) (order : Order) (input : Bytes) : Option Outboard := do
  let (size, fields) ← Bao.decode .outboard input
  let source := Bao.positioned (Bao.Encoding.outboard.layout size) fields
  let body ← writeSlots (fun slot => (source.find? (fun entry => entry.1 == slot)).map Prod.snd)
    (outboardLayout order size)
  readMemory root size order body

/-- A canonical Postcard u64 is a base-128 little-endian varint of at most ten bytes.
We reject nonminimal encodings, overflows and EOF; this is not a general Postcard decoder. -/
def readVarAt : Nat → Nat → Nat → Bytes → Option (Nat × Bytes)
  | fuel + 1, factor, base, byte :: rest =>
    let octet := byte.toNat
    let value := base + (octet % 128) * factor
    if value ≥ u64Limit then none
    else if octet < 128 then
      if factor != 1 && octet == 0 then none else some (value, rest)
    else readVarAt fuel (factor * 128) value rest
  | _, _, _, _ => none

def readVar : Bytes → Option (Nat × Bytes) := readVarAt 10 1 0

def writeVarAt : Nat → Nat → Bytes
  | 0, _ => []
  | fuel + 1, value =>
    if value < 128 then [UInt8.ofNat value]
    else UInt8.ofNat (128 + value % 128) :: writeVarAt fuel (value / 128)

def writeVar : Nat → Bytes := writeVarAt 10

def readMany {α : Type} (read : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, input => some ([], input)
  | count + 1, input => do
    let (item, rest) ← read input
    let (items, tail) ← readMany read count rest
    return (item :: items, tail)

def readVector {α : Type} (read : Bytes → Option (α × Bytes)) (input : Bytes) :
    Option (List α × Bytes) := do
  let (count, rest) ← readVar input
  if count > rest.length then none else readMany read count rest

def widthRun : Bytes → Option ((Nat × List Nat) × Bytes) := fun input => do
  let (offset, rest) ← readVar input
  let (widths, tail) ← readVector readVar rest
  return ((offset, widths), tail)

/-- Change points. Before the first change the range is empty; after the last, it repeats. -/
abbrev RangeSeq := List (Nat × Boundaries)

def changePoints (previous : Boundaries) (base : Nat) (first : Bool) :
    List (Nat × List Nat) → Option RangeSeq
  | [] => some []
  | (delta, widths) :: rest => do
    let offset := base + delta
    if offset ≥ u64Limit || (!first && delta == 0) then none else
      let query ← boundaries 0 widths
      if query == previous then none else
        return (offset, query) :: (← changePoints query offset false rest)

def queryAt (ranges : RangeSeq) (offset : Nat) : Boundaries :=
  ranges.foldl (fun query (index, next) => if index ≤ offset then next else query) []

def deltas (base : Nat) : List Nat → List Nat
  | [] => []
  | index :: rest => (index - base) :: deltas index rest

def writeChanges (base : Nat) : RangeSeq → Bytes
  | [] => []
  | (index, query) :: rest =>
    writeVar (index - base) ++ writeVar query.length ++ (deltas 0 query).flatMap writeVar ++
      writeChanges index rest

structure Get where
  hash : Hash
  ranges : RangeSeq
  deriving DecidableEq, Repr

def Get.blob (hash : Hash) : Get := ⟨hash, [(0, [0]), (1, [])]⟩
def Get.all (hash : Hash) : Get := ⟨hash, [(0, [0])]⟩

def readHash (input : Bytes) : Option (Hash × Bytes) := do
  let (raw, rest) ← takeExact 32 input
  let digest ← Bao.digest? raw
  return (⟨digest⟩, rest)

def readGet (input : Bytes) : Option Get := do
  let 0 :: body := input | none
  let (hash, body) ← readHash body
  let (runs, rest) ← readVector widthRun body
  if !rest.isEmpty then none else
    return ⟨hash, ← changePoints [] 0 true runs⟩

/-- Serialize normalized change points. For unchecked inputs use `readGet`/`changePoints`
first; this writer does not canonicalize arbitrary offsets or boundary lists. -/
def writeGet (request : Get) : Bytes :=
  0 :: (request.hash.bytes.toArray.toList ++ writeVar request.ranges.length ++
    writeChanges 0 request.ranges)

/-- HashSeq bytes have no header, tag or count. They are data authenticated under the
parent hash before child identifiers can be trusted. -/
def readHashSeq (input : Bytes) : Option (List Hash) := do
  let (hashes, rest) ← readMany readHash (input.length / 32) input
  if rest.isEmpty then some hashes else none

structure Transfer where
  offset : Nat
  hash : Hash
  query : Boundaries
  deriving Repr

/-- The depth-one Get schedule. `children` must come from an independently authenticated
HashSeq, not from an arbitrary server assertion. Raw Get sets `children` to `[]`. -/
def transfers (request : Get) (children : List Hash) : List Transfer :=
  ((request.hash :: children).zipIdx).filterMap fun (hash, offset) =>
    let query := queryAt request.ranges offset
    if query.isEmpty then none else some ⟨offset, hash, query⟩

structure Received where
  transfer : Transfer
  events : List Bao.Event
  edgeClaim : Option Nat

/-- Check an already delimited stream against its transfer schedule at the claimed extents.
These are internal candidates, not a public release decision. For a live stream use
`beginResponse` and `Bao.readStep`; a successful prefix is not a successful Get. -/
def verifyTransfers (ops : Bao.HashOps) : List Transfer → Bytes → Option (List Received)
  | [], input => if input.isEmpty then some [] else none
  | transfer :: rest, input => do
    let (size, fields, tail) ← readResponse transfer.query input
    let state := Bao.start (responsePlan size transfer.query) transfer.hash.bytes
    let (events, final) ← Bao.runSteps ops size state fields
    if !Bao.finished final [] true then none else
      return ⟨transfer, events, Bao.rightEdgeClaim size final⟩ ::
        (← verifyTransfers ops rest tail)

/-- CollectionV0's first HashSeq link is the metadata blob, the rest are item blobs. -/
def collectionLinks : List Hash → Option (Hash × List Hash)
  | metadata :: items => some (metadata, items)
  | [] => none

def readName (input : Bytes) : Option (String × Bytes) := do
  let (size, body) ← readVar input
  let (raw, rest) ← takeExact size body
  let name ← String.fromUTF8? ⟨raw.toArray⟩
  return (name, rest)

def readCollectionNames (input : Bytes) : Option (List String) := do
  let (header, body) ← takeExact 13 input
  if header != "CollectionV0.".toUTF8.data.toList then none else
    let (names, tail) ← readVector readName body
    if tail.isEmpty then some names else none

/-- Join already authenticated child names and links. Reject count mismatches rather
than silently dropping an unmatched link or name. -/
def collectionItems (links : List Hash) (metadata : Bytes) : Option (List (String × Hash)) := do
  let (_, children) ← collectionLinks links
  let names ← readCollectionNames metadata
  if names.length = children.length then some (names.zip children) else none

end Silmaril.Formats.Iroh
