module

import Silmaril.Formats.Dasl.IndexSequence.Thms
meta import Silmaril.Formats.Dasl.IndexSequence.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.IndexSequence

private def index : Encode.TotalCodec Nat (Shallow String) :=
  ⟨fun count => Encode.list.encode (List.replicate count .null),
    fun tree => (Encode.list.decode? tree).map List.length,
    fun count => by rw [Encode.list.recovers]; simp⟩

private def width : { size : Nat // 0 < size } := ⟨2, by decide⟩
private def rows : Entries String := [("alpha", 0), ("beta", 0), ("alpha", 1), ("gamma", 2), ("delta", 0)]
private def flatRows := flat (entryCodec Encode.text index)
private def flatColumns := parallel (flat Encode.text) (flat index)
private def pagedColumns := parallel (paged width Encode.text) (paged width index)

example : (pageContents width).encode rows = [rows.take 2, (rows.drop 2).take 2, rows.drop 4] := by decide

private def expect (success : Bool) (label : String) : IO Unit :=
  unless success do throw (IO.userError label)

public def main : IO Unit := do
  expect (pagedColumns.decode? (pagedColumns.encode rows) == some rows &&
    flatColumns.decode? (flatColumns.encode rows) == some rows &&
    flatRows.decode? (flatRows.encode rows) == some rows) "flat, paged and row contents"
  expect (((checked .orderedParent pagedColumns).decode? (pagedColumns.encode rows)).map Subtype.val == some rows)
    "checked parent occurrences"
  expect (((check? .orderedParent rows).bind asMap?).isNone) "global map uniqueness across pages"
  let columns := rawColumns (flat Encode.text) (flat index)
  expect ((flatColumns.decode? (columns.encode ⟨["alpha", "beta"], [0]⟩)).isNone) "short e column"
  expect ((flatColumns.decode? (columns.encode ⟨["alpha"], [0, 1]⟩)).isNone) "short t column"
  expect (((checked .orderedParent flatColumns).decode? (flatColumns.encode [("alpha", 1), ("beta", 0)])).isNone)
    "parent cycle"
  let classes := checked (.classId 2) flatRows
  expect ((classes.decode? (flatRows.encode [("alpha", 1)])).isSome) "class may exceed row index"
  expect ((classes.decode? (flatRows.encode [("alpha", 2)])).isNone) "out of range class"
  let pages := Encode.listOf (Encode.listOf index)
  expect (((paged width index).decode? (pages.encode [[], [0]])).isNone) "empty page"
  expect (((paged width index).decode? (pages.encode [[0], [1, 2]])).isNone) "short interior page"
  expect (((paged width index).decode? (pages.encode [[0, 1, 2]])).isNone) "oversized page"
  expect (((entryCodec Encode.text index).decode? (.list 1 fun _ => .string "alpha")).isNone) "entry arity"
  expect ((flatColumns.decode? (.dict {"t"} fun _ => (flat Encode.text).encode ["alpha"])).isNone) "missing e field"
