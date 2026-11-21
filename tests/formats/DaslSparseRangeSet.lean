module

import Silmaril.Formats.Dasl.SparseRangeSet.Thms
import Silmaril.Formats.Dasl.Wire.Profile.Thms
meta import Silmaril.Formats.Dasl.SparseRangeSet.Thms
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs

open Silmaril.Formats.Dasl

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def interval (lower upper : Int64) : IO SparseRangeSet.Interval :=
  match SparseRangeSet.Interval.fromEndpoints? lower upper with
  | some range => pure range
  | none => throw (IO.userError "expected valid interval fixture")

private def checkLayout {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let layout := SparseRangeSet.normalize
    [← interval 3 7, ← interval (-3) (-1), ← interval 0 2, ← interval 7 8, ← interval 10 10]
  let expected := SparseRangeSet.normalize [← interval (-3) 8, ← interval 10 10]
  check (decide (layout = expected)) "normalize overlaps, adjacency and input order"
  check (layout.ranges.length == 2 && SparseRangeSet.cardinality layout == 13) "two maximal runs, 13 points"
  check (SparseRangeSet.contains layout 0 && !SparseRangeSet.contains layout 9) "inside and gap membership"
  let codec := profile.codec SparseRangeSet.codec
  let golden : ByteArray := ⟨#[0x82, 0x82, 0x22, 0x08, 0x82, 0x0a, 0x0a]⟩
  check (codec.encode? layout == some golden && decide (codec.decode? golden = some layout)) "golden range array"
  check (codec.encode? (SparseRangeSet.normalize []) == some ⟨#[0x80]⟩) "empty range set"
  check ((codec.decode? ⟨#[0x81, 0x82, 0x01, 0x00]⟩).isNone) "reversed interval rejected"
  check ((codec.decode? ⟨#[0x82, 0x82, 0x00, 0x00, 0x82, 0x01, 0x01]⟩).isNone) "adjacent ranges rejected"
  check ((codec.decode? ⟨#[0x82, 0x82, 0x00, 0x01, 0x82, 0x01, 0x02]⟩).isNone) "overlapping ranges rejected"
  check ((codec.decode? ⟨#[0x82, 0x82, 0x03, 0x03, 0x82, 0x00, 0x00]⟩).isNone) "descending ranges rejected"
  check ((codec.decode? ⟨#[0x81, 0x81, 0x00]⟩).isNone) "malformed pair rejected"
  let minimum := Int64.minValue
  let maximum := Int64.maxValue
  let edges := SparseRangeSet.normalize [← interval maximum maximum, ← interval minimum minimum]
  check (edges.ranges.length == 2 && SparseRangeSet.cardinality edges == 2) "signed edges do not wrap or join"
  let full := SparseRangeSet.normalize [← interval 0 maximum, ← interval minimum (-1)]
  check (full.ranges.length == 1 && SparseRangeSet.cardinality full == 2^64) "full signed domain cardinality"
  let some fullWire := codec.encode? full | throw (IO.userError "full signed domain serializes")
  check (fullWire.size == 20 && decide (codec.decode? fullWire = some full)) "both endpoints recover from 20 bytes"

public def main : IO Unit := do
  checkLayout Wire.Profile.dasl
  checkLayout Wire.Profile.bdasl
