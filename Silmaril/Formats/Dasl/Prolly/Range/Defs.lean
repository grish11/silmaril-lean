module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Semantics.Prolly.Routing.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly.Range

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Node)

variable {Name Key Payload : Type} [LinearOrder Key]

def includes (lower upper key : Key) : Bool := decide (lower ≤ key ∧ key < upper)

def mapSlice (lower upper : Key) (map : OrderedMap Key Payload) : OrderedMap Key Payload :=
  ⟨map.entries.filter fun entry => includes lower upper entry.1, map.ordered.sublist List.filter_sublist⟩

structure Result (Key Payload : Type) where
  entries : List (Key × Payload)
  visits : Nat
  deriving DecidableEq

/-- Retain the first edge with an inclusive maximum at least `upper`, but
omit every subsequent edge. Their keys lie strictly above that separator in
an ordered tree with truthful separators. -/
def throughUpper {Child : Type} (upper : Key) : List (Key × Child) → List (Key × Child)
  | [] => []
  | child :: rest => child :: if upper ≤ child.1 then [] else throughUpper upper rest

def selectedChildren {Child : Type} (cutoff : Option Key) (children : List (Key × Child)) : List (Key × Child) :=
  cutoff.elim children (fun upper => throughUpper upper children)

/-- Selected block occurrences in the reference tree, not distinct addresses,
byte traffic or comparison cost. -/
def selectedVisitsWith (lower : Key) (cutoff : Option Key) : (level : Nat) → Node Key Payload level → Nat
  | 0, _ => 1
  | level + 1, children => 1 + ((selectedChildren cutoff children).map fun child =>
      if lower ≤ child.1 then selectedVisitsWith lower cutoff level child.2 else 0).sum

def selectedVisits (lower : Key) : (level : Nat) → Node Key Payload level → Nat :=
  selectedVisitsWith lower none

/-- Scan `[lower, upper)` in ascending order. Skip maxima below `lower` and
optionally the suffix past the upper fence. Trustworthy pruning requires
truthful separators. A selected child fault aborts the whole answer. -/
def scanWith (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) (lower upper : Key)
    (pruneUpper : Bool) :
    (fuel : Nat) → Option Nat → Name → Except (Fault Name) (Result Key Payload)
  | 0, _, name => .error (.fuel name)
  | fuel + 1, expected, name => do
    match ← read name with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ width ∧
          entries.Pairwise (fun left right => left.1 < right.1) then
        .ok ⟨entries.filter fun entry => includes lower upper entry.1, 1⟩
      else .error (.invalidNode name)
    | .branch level children =>
      if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧ children.length ≤ width ∧
          children.Pairwise (fun left right => left.1 < right.1) then do
        let groups ← (selectedChildren (if pruneUpper then some upper else none) children).mapM fun child =>
          if lower ≤ child.1 then scanWith read width lower upper pruneUpper fuel (some (level - 1)) child.2
          else .ok ⟨[], 0⟩
        .ok ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩
      else .error (.invalidNode name)

/-- The original lower-pruned scan, including its original fault behavior. -/
def scan (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) (lower upper : Key) :
    Nat → Option Nat → Name → Except (Fault Name) (Result Key Payload) :=
  scanWith read width lower upper false

/-- Prune with both bounds, with a half-open interval `[lower, upper)`. The
boundary child itself may still contain in-range keys and must be examined. -/
def scanTwoSided (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) (lower upper : Key) :
    Nat → Option Nat → Name → Except (Fault Name) (Result Key Payload) :=
  scanWith read width lower upper true

/-- Contained-entry comparison over the two intervals, not key-domain inclusion.
Only two successful scans may produce a Boolean. This is a reference comparison
of the materialized slices, not a shared-block or streaming algorithm. -/
def intervalSubmap [DecidableEq Payload] (left right : Name → Except (Fault Name) (Block Name Key Payload))
    (width fuel : Nat) (lower upper : Key) (leftRoot rightRoot : Name) : Except (Fault Name) Bool := do
  let leftSlice ← scanTwoSided left width lower upper fuel none leftRoot
  let rightSlice ← scanTwoSided right width lower upper fuel none rightRoot
  pure (leftSlice.entries.all fun entry => decide (rightSlice.entries.lookup entry.1 = some entry.2))

end Silmaril.Formats.Dasl.Prolly.Range
