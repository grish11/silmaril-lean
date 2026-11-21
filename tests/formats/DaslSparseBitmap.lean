module

import Silmaril.Formats.Dasl.SparseBitmap.Thms
import Silmaril.Formats.Dasl.Wire.Profile.Thms
meta import Silmaril.Formats.Dasl.SparseBitmap.Thms
meta import Silmaril.Formats.Dasl.Wire.Profile.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.SparseBitmap

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def bitmapTests {Name : Type} (profile : Wire.Profile Name) : IO Unit := do
  let last : UInt64 := 0xffffffffffffffff
  let raw := [(last, 4), (1, 0x83), (1, 4), (0, 0), (2, 0x80)]
  let layout : Layout 2 := normalizePages raw
  let expected : Layout 2 := normalize [(1, 0), (1, 1), (1, 2), (last, 2)]
  check (decide (layout = expected)) "duplicates union; padding and empty pages disappear"
  check (pageCount layout == 2 && cardinality layout == 4) "count sparse pages and bits separately"
  check (contains layout (last, 2) && !contains layout (last, 1) && !contains layout (0, 0)) "lookup by page and offset"
  let wire := profile.codec (codec (width := 2))
  let golden : ByteArray := ⟨#[0x82, 0x82, 0x01, 0x41, 0x07, 0x82, 0x20, 0x41, 0x04]⟩
  check (wire.encode? layout == some golden && decide (wire.decode? golden = some layout)) "bitmap wire recovery"
  check (wire.encode? (normalize []) == some ⟨#[0x80]⟩) "empty bitset has no pages"
  for (label, bytes) in [
      ("empty page", #[0x81, 0x82, 0x00, 0x41, 0x00]),
      ("nonzero padding", #[0x81, 0x82, 0x00, 0x41, 0x81]),
      ("overlong mask", #[0x81, 0x82, 0x00, 0x42, 0x01, 0x00]),
      ("duplicate page", #[0x82, 0x82, 0x00, 0x41, 0x01, 0x82, 0x00, 0x41, 0x02]),
      ("descending pages", #[0x82, 0x82, 0x20, 0x41, 0x01, 0x82, 0x01, 0x41, 0x02])] do
    check (wire.decode? ⟨bytes⟩).isNone (label ++ " rejected on wire")
  let full := profile.codec (codec (width := 7))
  let high : Layout 7 := normalize [(0, 7)]
  let highBytes : ByteArray := ⟨#[0x81, 0x82, 0x00, 0x41, 0x80]⟩
  check (full.encode? high == some highBytes && decide (full.decode? highBytes = some high)) "bit seven is usable at width eight"

public def main : IO Unit := do
  bitmapTests Wire.Profile.dasl
  bitmapTests Wire.Profile.bdasl
