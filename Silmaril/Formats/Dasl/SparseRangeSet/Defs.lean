module

public import Mathlib.Data.Int.Interval
public import Silmaril.Formats.Dasl.SparseIntSet.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.SparseRangeSet

/-- Inclusive signed endpoints. Arithmetic on them is widened to `Int`. -/
structure Interval where
  lower : Int64
  upper : Int64
  ordered : lower.toInt ≤ upper.toInt
  deriving DecidableEq

namespace Interval

def fromEndpoints? (lower upper : Int64) : Option Interval :=
  if ordered : lower.toInt ≤ upper.toInt then some ⟨lower, upper, ordered⟩ else none

def singleton (key : Int64) : Interval := ⟨key, key, le_rfl⟩

def Includes (interval : Interval) (point : Int) : Prop :=
  interval.lower.toInt ≤ point ∧ point ≤ interval.upper.toInt

instance (interval : Interval) (point : Int) : Decidable (interval.Includes point) :=
  inferInstanceAs (Decidable (_ ≤ point ∧ point ≤ _))

/-- At least one uncovered integer lies between the two intervals. -/
def Before (left right : Interval) : Prop := left.upper.toInt + 1 < right.lower.toInt

instance (left right : Interval) : Decidable (left.Before right) :=
  inferInstanceAs (Decidable (left.upper.toInt + 1 < right.lower.toInt))

def hull (left right : Interval) : Interval where
  lower := Int64.ofIntLE (min left.lower.toInt right.lower.toInt)
    (le_min left.lower.minValue_le_toInt right.lower.minValue_le_toInt)
    ((min_le_left ..).trans left.lower.toInt_le)
  upper := Int64.ofIntLE (max left.upper.toInt right.upper.toInt)
    (left.upper.minValue_le_toInt.trans (le_max_left ..))
    (max_le left.upper.toInt_le right.upper.toInt_le)
  ordered := by simpa using (min_le_left ..).trans (left.ordered.trans (le_max_left ..))

def cardinality (interval : Interval) : Nat := (interval.upper.toInt + 1 - interval.lower.toInt).toNat

def wideMembers (interval : Interval) : Finset Int := Finset.Icc interval.lower.toInt interval.upper.toInt

def key (interval : Interval) (point : interval.wideMembers) : Int64 :=
  Int64.ofIntLE point.val
    (interval.lower.minValue_le_toInt.trans (Finset.mem_Icc.mp point.property).1)
    ((Finset.mem_Icc.mp point.property).2.trans interval.upper.toInt_le)

/-- Finite-set semantics; membership and cardinality do not need to enumerate this. -/
def members (interval : Interval) : Finset Int64 := interval.wideMembers.attach.map
  ⟨interval.key, fun _ _ same => Subtype.ext (by simpa [key] using congrArg Int64.toInt same)⟩

def codec {Name : Type} : Encode.TotalCodec Interval (Shallow Name) :=
  let endpoints : Encode.TotalCodec Interval (Int64 × Int64) :=
    ⟨fun interval => (interval.lower, interval.upper), (fun pair => fromEndpoints? pair.1 pair.2),
      fun ⟨_, _, ordered⟩ => by simp [fromEndpoints?, ordered]⟩
  endpoints.then ((Encode.signed.prod Encode.signed).then Encode.pairEntry)

end Interval

open Silmaril.Formats.Dasl.SparseRangeSet.Interval

/-- Strict separation implies disjointness and rules out nonmaximal adjacent runs. -/
@[ext] structure Layout where
  ranges : List Interval
  separated : ranges.Pairwise Before
  deriving DecidableEq

def fromRanges? (ranges : List Interval) : Option Layout :=
  if separated : ranges.Pairwise Before then some ⟨ranges, separated⟩ else none

def Covers (ranges : List Interval) (point : Int) : Prop :=
  ∃ interval ∈ ranges, interval.Includes point

/-- Insert into an already separated list, merging overlaps and adjacency. -/
def insertRange (newRange : Interval) : List Interval → List Interval
  | [] => [newRange]
  | head :: tail =>
    if newRange.Before head then newRange :: head :: tail
    else if head.Before newRange then head :: insertRange newRange tail
    else insertRange (newRange.hull head) tail

def mergeRanges (ranges : List Interval) : List Interval := ranges.foldr insertRange []

def contains (layout : Layout) (key : Int64) : Bool :=
  layout.ranges.any (fun interval => decide (interval.Includes key.toInt))

def cardinality (layout : Layout) : Nat := (layout.ranges.map Interval.cardinality).sum

def members (layout : Layout) : Finset Int64 :=
  layout.ranges.foldr (fun interval rest => interval.members ∪ rest) ∅

/-- One shallow block containing a list of ordered `[lower, upper]` pairs. -/
def codec {Name : Type} : Encode.TotalCodec Layout (Shallow Name) :=
  let rangesCodec : Encode.TotalCodec Layout (List Interval) :=
    ⟨Layout.ranges, fromRanges?, fun ⟨_, separated⟩ => by simp [fromRanges?, separated]⟩
  rangesCodec.then (Encode.listOf Interval.codec)

end Silmaril.Formats.Dasl.SparseRangeSet
