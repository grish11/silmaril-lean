module

public import Silmaril.Formats.Parquet.OffsetIndex.Defs

/-! Pure row-window planning over checked Parquet page locations. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.OffsetIndex.Window

/-- A nonempty group-relative row interval and its original indexed page. -/
structure Clip where
  page : Entry
  first : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- Half-open row bounds relative to the start of the original page. -/
def Clip.localBounds (clip : Clip) : Nat × Nat :=
  (clip.first - clip.page.location.firstRow, clip.stop - clip.page.location.firstRow)

/-- Intersect a group-relative window with the page's half-open row interval. -/
def clip (first stop : Nat) (page : Entry) : Option Clip :=
  let lower := max first page.location.firstRow
  let upper := min stop page.rowStop
  if lower < upper then some ⟨page, lower, upper⟩ else none

/-- Keep an ordered clip for each intersected page. On a checked index, an
empty, reversed or out-of-group window produces an empty plan. A stop
past the group end clips to the available rows. -/
def plan (first stop : Nat) (index : Index) : List Clip :=
  index.pages.filterMap (clip first stop)

/-- Validate the selected index on the immutable snapshot before planning.
An absent index gives `ok none`. A present index with no matching rows gives
`ok (some [])`. Index validation errors propagate for every window. -/
def planChecked (limits : Limits) (snapshot : Snapshot.Checked)
    (group column first stop : Nat) : Except Error (Option (List Clip)) :=
  (OffsetIndex.validate limits snapshot group column).map (Option.map (plan first stop))

end Silmaril.Formats.Parquet.OffsetIndex.Window
