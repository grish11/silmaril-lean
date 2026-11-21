module

import Silmaril.Semantics.Rope.Thms
meta import Silmaril.Semantics.Rope.Thms

open Silmaril.Semantics.Rope

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def childPageCounts {Cell : Type} : Tree Cell → List Nat
  | .branch count children => List.ofFn (n := count) fun index => (children index).pages.length
  | _ => []

public def main : IO Unit := do
  let left : Geometry := ⟨2, by decide, 0, .left⟩
  let right := { left with bias := .right }
  let wide := { left with exponent := 2 }
  let first : Tree Nat := .leaf [0, 1, 2, 3]
  let middle : Tree Nat := .leaf [4]
  let last : Tree Nat := .leaf [5, 6, 7, 8]
  let expected := List.range 9
  let leftRaw := (first.concat middle).concat last
  let rightRaw := first.concat (middle.concat last)
  let packedLeft := normalize left leftRaw
  let packedRight := normalize right rightRaw
  let packedWide := normalize wide leftRaw
  check (packedLeft.flatten == expected && packedRight.flatten == expected && packedWide.flatten == expected)
    "exact cells recovered from both raw associations and all normal forms"
  check (packedLeft.pages.map List.length == [2, 2, 2, 2, 1] && packedRight.pages == packedLeft.pages)
    "full payload pages and one trailing subpage"
  check (childPageCounts packedLeft == [4, 1] && childPageCounts packedRight == [1, 4]) "left/right branch bias"
  check (packedLeft.depth == 3 && packedRight.depth == 3 && packedWide.depth == 1) "binary and eight-way depth"
  check (packedLeft.size == 9 && childPageCounts packedWide == [1, 1, 1, 1, 1]) "size and sparse final branch"
  check ((normalize left (Tree.leaf ([] : List Nat))).pages.isEmpty) "empty leaf disappears"
  let bytes : ByteArray := ⟨#[0xff, 0, 0x80]⟩
  check (toBytes (ofBytes left bytes) == bytes) "raw bytes need not be UTF-8"
  let text := "é💡"
  let textRope := ofString left text
  check (toString textRope == text && textRope.size == 2 && text.utf8ByteSize == 6) "text pages count characters"
