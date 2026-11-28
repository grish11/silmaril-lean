module

public import Batteries.Data.List.Basic
public import Silmaril.Formats.Bytes
public import Silmaril.Numeric.TimeZone.Defs
public import Silmaril.Prelude.Bytes.Digits.Defs

/-! # Bounded TZif version 2 and 3 explicit transition data -/

@[expose] public section

namespace Silmaril.Formats.TZif

open Numeric.Timestamp Numeric.TimeZone

inductive Version where
  | v2 | v3
  deriving DecidableEq, Repr

inductive Error where
  | sizeLimit
  | truncated
  | header
  | version
  | counts
  | leapSeconds
  | footer
  | designation
  | indicator
  | offset
  | transitionType
  | transitionOrder
  deriving DecidableEq, Repr

/-- The six unsigned count fields of either header, in their wire order. -/
structure Counts where
  utLocal : Nat
  standardWall : Nat
  leaps : Nat
  times : Nat
  types : Nat
  designations : Nat
  deriving DecidableEq, Repr

def Counts.blockSize (counts : Counts) (timeSize : Nat) : Nat :=
  counts.times * timeSize + counts.times + counts.types * 6 + counts.designations +
    counts.leaps * (timeSize + 4) + counts.standardWall + counts.utLocal

structure Layout where
  version : Version
  compatibility : Counts
  selected : Counts
  deriving DecidableEq, Repr

namespace Layout

def secondHeader (layout : Layout) : Nat := 44 + layout.compatibility.blockSize 4

def blockStart (layout : Layout) : Nat := layout.secondHeader + 44

def blockEnd (layout : Layout) : Nat := layout.blockStart + layout.selected.blockSize 8

def indexStart (layout : Layout) : Nat := layout.blockStart + layout.selected.times * 8

def typeStart (layout : Layout) : Nat := layout.indexStart + layout.selected.times

def designationStart (layout : Layout) : Nat := layout.typeStart + layout.selected.types * 6

def standardStart (layout : Layout) : Nat :=
  layout.designationStart + layout.selected.designations + layout.selected.leaps * 12

def universalStart (layout : Layout) : Nat := layout.standardStart + layout.selected.standardWall

end Layout

namespace Internal

/-- Used only after a header or block range check. -/
def octets (file : Bytes) (start length : Nat) : List UInt8 :=
  (Bytes.mk (file.data.extract start (start + length))).toList

def unsignedBE (file : Bytes) (start width : Nat) : Nat :=
  KBytes.leVal (octets file start width).reverse

def signedBE (file : Bytes) (start width : Nat) : Int :=
  let value := unsignedBE file start width
  if value < 2 ^ (8 * width - 1) then value else (value : Int) - 2 ^ (8 * width)

def byte (file : Bytes) (index : Nat) : Except Error UInt8 :=
  match file.data[index]? with
  | some value => .ok value
  | none => .error .truncated

def header (file : Bytes) (start : Nat) : Except Error (Version × Counts) := do
  if file.length < start + 44 then throw .truncated
  if octets file start 4 != [0x54, 0x5a, 0x69, 0x66] ||
      !(octets file (start + 5) 15).all (· == 0) then throw .header
  let version ← match ← byte file (start + 4) with
    | 0x32 => pure Version.v2
    | 0x33 => pure Version.v3
    | _ => throw .version
  let readCount := fun index => unsignedBE file (start + 20 + 4 * index) 4
  let counts : Counts := ⟨readCount 0, readCount 1, readCount 2, readCount 3, readCount 4, readCount 5⟩
  if counts.leaps != 0 then throw .leapSeconds
  if counts.types = 0 ∨ 256 < counts.types ∨ counts.designations = 0 ∨
      (counts.utLocal ≠ 0 ∧ counts.utLocal ≠ counts.types) ∨
      (counts.standardWall ≠ 0 ∧ counts.standardWall ≠ counts.types) then throw .counts
  return (version, counts)

end Internal

/-- Select the second header by the checked 32-bit layout. The file budget
    applies before either block is decoded, and both footer delimiters must fit. -/
def locate (maxBytes : Nat) (file : Bytes) : Except Error Layout :=
  if maxBytes < file.length then .error .sizeLimit else do
    let (version, compatibility) ← Internal.header file 0
    let (selectedVersion, selected) ← Internal.header file (44 + compatibility.blockSize 4)
    let layout : Layout := ⟨version, compatibility, selected⟩
    if version ≠ selectedVersion then .error .version
    else if file.length < layout.blockEnd + 2 then .error .truncated
    else .ok layout

structure LocalType where
  offsetSeconds : Int
  isDst : Bool
  designation : List UInt8
  standard : Bool
  universal : Bool
  deriving DecidableEq, Repr

/-- RFC 9636 reserves the designation `-00` for unspecified local time. -/
def LocalType.specified (kind : LocalType) : Bool := kind.designation != [0x2d, 0x30, 0x30]

/-- The index is checked against the selected block's actual type array. -/
structure TransitionEntry (types : Array LocalType) where
  second : Int
  index : Fin types.size
  deriving Repr

def TransitionEntry.localType {types : Array LocalType} (entry : TransitionEntry types) : LocalType :=
  types[entry.index]

def TransitionEntry.toTransition {types : Array LocalType} (entry : TransitionEntry types) : Transition :=
  ⟨(⟨entry.second⟩ : Ticks .utcInstant .second).denote, Offset.ofSeconds entry.localType.offsetSeconds⟩

structure Block where
  layout : Layout
  types : Array LocalType
  transitions : List (TransitionEntry types)
  ordered : transitions.IsChain (fun first second => first.second < second.second)
  /-- Footer bytes excluding the two newlines. The POSIX rules are opaque here. -/
  footer : List UInt8

namespace Internal

def flag (file : Bytes) (start index count : Nat) : Except Error Bool := do
  if count = 0 then return false
  match ← byte file (start + index) with
  | 0 => return false
  | 1 => return true
  | _ => throw .indicator

def localType (file : Bytes) (layout : Layout) (designations : List UInt8) (index : Nat) :
    Except Error LocalType := do
  let start := layout.typeStart + 6 * index
  let offset := signedBE file start 4
  if offset = -(2 ^ 31 : Int) then throw .offset
  let dst ← flag file (start + 4) 0 1
  let designationIndex := (← byte file (start + 5)).toNat
  if designations.length ≤ designationIndex then throw .designation
  let standard ← flag file layout.standardStart index layout.selected.standardWall
  let universal ← flag file layout.universalStart index layout.selected.utLocal
  if universal && !standard then throw .indicator
  return ⟨offset, dst, (designations.drop designationIndex).takeWhile (· != 0), standard, universal⟩

def transition (file : Bytes) (layout : Layout) (types : Array LocalType) (index : Nat) :
    Except Error (TransitionEntry types) := do
  let typeIndex := (← byte file (layout.indexStart + index)).toNat
  if h : typeIndex < types.size then
    return ⟨signedBE file (layout.blockStart + 8 * index) 8, ⟨typeIndex, h⟩⟩
  else throw .transitionType

def footer (file : Bytes) (layout : Layout) : Except Error (List UInt8) := do
  if (← byte file layout.blockEnd) != 10 || (← byte file (file.length - 1)) != 10 then
    throw .footer
  let text := octets file (layout.blockEnd + 1) (file.length - layout.blockEnd - 2)
  if !text.all (fun b => 32 ≤ b.toNat && b.toNat ≤ 126) then throw .footer
  return text

end Internal

/-- Parse only the selected 64-bit block and the footer framing. -/
def parse (maxBytes : Nat) (file : Bytes) : Except Error Block := do
  let layout ← locate maxBytes file
  let text ← Internal.footer file layout
  let designations := Internal.octets file layout.designationStart layout.selected.designations
  if designations.getLast? = some 0 then
    let typeList ← (List.range layout.selected.types).mapM (Internal.localType file layout designations)
    let types := typeList.toArray
    let transitions ← (List.range layout.selected.times).mapM (Internal.transition file layout types)
    if h : transitions.IsChain (fun first second => first.second < second.second) then
      .ok ⟨layout, types, transitions, h, text⟩
    else .error .transitionOrder
  else .error .designation

namespace Block

/-- The last explicit transition at or before the boundary, or type zero. -/
def typeAtStart? (block : Block) (start : Int) : Option LocalType :=
  match (block.transitions.takeWhile (fun entry => entry.second ≤ start)).getLast? with
  | some entry => some entry.localType
  | none => block.types[0]?

def interior (block : Block) (start stop : Int) : List (TransitionEntry block.types) :=
  block.transitions.filter (fun entry => start < entry.second && entry.second < stop)

/-- Using the last transition as an exclusive ceiling leaves any POSIX tail
    semantics to a later profile. With no transitions, only an empty footer
    admits a constant type-zero interval. -/
def permitsStop (block : Block) (stop : Int) : Bool :=
  match block.transitions.getLast? with
  | some entry => decide (stop ≤ entry.second)
  | none => block.footer.isEmpty

/-- Construct a schedule only for the requested half-open interval. -/
def toSchedule? (block : Block) (start stop : Ticks .utcInstant .second) : Option Schedule :=
  if block.permitsStop stop.ticks then
    match block.typeAtStart? start.ticks with
    | none => none
    | some initial =>
      let interior := block.interior start.ticks stop.ticks
      if initial.specified && interior.all (·.localType.specified) then
        Schedule.ofTransitions? start.denote stop.denote (Offset.ofSeconds initial.offsetSeconds)
          (interior.map TransitionEntry.toTransition)
      else none
  else none

end Block

end Silmaril.Formats.TZif
