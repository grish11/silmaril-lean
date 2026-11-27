module

public import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
public import Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Defs

/-! The RFC 7932 compressed meta-block header from NBLTYPESL through
the three payload tree groups. The enclosing decoder supplies the
cursor after stream and meta-block framing. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.CompressedHeader

open ContextMap.Decode (Map)
open Huffman.Description (Table)

structure Limits where
  /-- Combined expanded entries of both maps, also bounding map symbol work. -/
  mapEntries : Nat
  /-- Combined number of descriptions in the three payload tree groups. -/
  trees : Nat
  /-- Committed header bits, from NBLTYPESL through the last distance tree. -/
  bits : Nat

inductive Group where
  | literal | insertCopy | distance
  deriving DecidableEq, Repr

def Group.alphabet (group : Group) (fields : ContextHeader.Fields) : Nat :=
  match group with
  | .literal => 256
  | .insertCopy => 704
  | .distance => fields.distanceAlphabet

def Group.count (group : Group) (initial : ContextHeader.Header) (literal distance : Map) : Nat :=
  match group with
  | .literal => literal.treeCount
  | .insertCopy => initial.controls.insertCopy.typeCount
  | .distance => distance.treeCount

structure Header where
  initial : ContextHeader.Header
  literalMap : Map
  distanceMap : Map
  literalTrees : List Table
  insertCopyTrees : List Table
  distanceTrees : List Table

def Header.tables (header : Header) : Group → List Table
  | .literal => header.literalTrees
  | .insertCopy => header.insertCopyTrees
  | .distance => header.distanceTrees

def mapExtent (kind : ContextMap.Kind) (initial : ContextHeader.Header) : Nat :=
  match kind with
  | .literal => kind.extent initial.controls.literal.typeCount
  | .distance => kind.extent initial.controls.distance.typeCount

def Header.mapEntries (header : Header) : Nat :=
  mapExtent .literal header.initial + mapExtent .distance header.initial

def Header.treeCount (header : Header) : Nat :=
  header.literalTrees.length + header.insertCopyTrees.length + header.distanceTrees.length

inductive Error where
  | initial (reason : ContextHeader.Error)
  | mapEntryLimit
  | map (kind : ContextMap.Kind) (reason : ContextMap.Decode.Error)
  | treeLimit
  | tree (group : Group) (ordinal : Nat) (reason : Huffman.Description.Error)
  deriving DecidableEq, Repr

inductive GroupWire (alphabet : Nat) : Nat → List Bool → List Table → Prop where
  | done : GroupWire alphabet 0 [] []
  | next {count : Nat} {bits tailBits : List Bool} {table : Table} {tail : List Table} :
      Huffman.Description.Wire alphabet bits table → table.alphabetSize = alphabet →
      GroupWire alphabet count tailBits tail →
      GroupWire alphabet (count + 1) (bits ++ tailBits) (table :: tail)

structure Wire (mapWork : Nat) (bits : List Bool) (header : Header) : Prop where
  parts : ∃ initialBits literalMapBits distanceMapBits literalTreeBits insertTreeBits distanceTreeBits
        literalWork distanceWork,
    bits = initialBits ++ literalMapBits ++ distanceMapBits ++ literalTreeBits ++
      insertTreeBits ++ distanceTreeBits ∧
    mapWork = literalWork + distanceWork ∧
    ContextHeader.Header.Wire initialBits header.initial ∧
    ContextMap.Decode.Wire (mapExtent .literal header.initial) literalWork literalMapBits header.literalMap ∧
    ContextMap.Decode.Wire (mapExtent .distance header.initial) distanceWork distanceMapBits header.distanceMap ∧
    GroupWire 256 header.literalMap.treeCount literalTreeBits header.literalTrees ∧
    GroupWire 704 header.initial.controls.insertCopy.typeCount insertTreeBits header.insertCopyTrees ∧
    GroupWire header.initial.fields.distanceAlphabet header.distanceMap.treeCount distanceTreeBits header.distanceTrees

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def Cursor.advance (cursor : Cursor) (after : LSBReader) : Cursor :=
  ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩

def readMap (kind : ContextMap.Kind) (types : Nat) (cursor : Cursor) :
    Except Error (Map × Cursor) := do
  let extent := kind.extent types
  let (map, after) ←
    (ContextMap.Decode.read kind types ⟨extent, extent, cursor.remaining⟩ cursor.reader).mapError (Error.map kind)
  pure (map, cursor.advance after)

def readGroup (group : Group) (alphabet : Nat) : Nat → Nat → Cursor → Except Error (List Table × Cursor)
  | 0, _, cursor => .ok ([], cursor)
  | count + 1, ordinal, cursor => do
    let (table, after) ←
      (Huffman.Description.read ⟨alphabet, cursor.remaining⟩ alphabet cursor.reader).mapError (Error.tree group ordinal)
    let (tail, final) ← readGroup group alphabet count (ordinal + 1) (cursor.advance after)
    pure (table :: tail, final)

end Internal

/-- Read the complete compressed header in RFC order. The standard
    window profile uses the RFC distance alphabet derived from the header. -/
def read (limits : Limits) (before : LSBReader) : Except Error (Header × LSBReader) := do
  let (initial, afterInitial) ← (ContextHeader.read limits.bits before).mapError Error.initial
  if limits.mapEntries < mapExtent .literal initial + mapExtent .distance initial then
    throw .mapEntryLimit
  else
    let cursor := (⟨before, limits.bits⟩ : Internal.Cursor).advance afterInitial
    let (literalMap, cursor) ← Internal.readMap .literal initial.controls.literal.typeCount cursor
    let (distanceMap, cursor) ← Internal.readMap .distance initial.controls.distance.typeCount cursor
    let literal := Group.literal.count initial literalMap distanceMap
    let insertCopy := Group.insertCopy.count initial literalMap distanceMap
    let distance := Group.distance.count initial literalMap distanceMap
    if limits.trees < literal + insertCopy + distance then
      throw .treeLimit
    else
      let (literalTrees, cursor) ← Internal.readGroup .literal (Group.literal.alphabet initial.fields) literal 0 cursor
      let (insertCopyTrees, cursor) ←
        Internal.readGroup .insertCopy (Group.insertCopy.alphabet initial.fields) insertCopy 0 cursor
      let (distanceTrees, cursor) ←
        Internal.readGroup .distance (Group.distance.alphabet initial.fields) distance 0 cursor
      pure (⟨initial, literalMap, distanceMap, literalTrees, insertCopyTrees, distanceTrees⟩, cursor.reader)

end Silmaril.Formats.Compression.Brotli.CompressedHeader
