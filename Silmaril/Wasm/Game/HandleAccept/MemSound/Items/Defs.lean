module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# A reader checker over a memory-returning `items` import

`itemsMod` imports `sexp.items : [i32 i32] → []` (import `0`: `items(h, retptr)`, which writes
the `list<i32>` of the children of `h` through the return pointer, canonical-ABI style: `(ptr,
len)` at `retptr`, the handles at `ptr`) and `sexp.accept : [i32] → []` (import `1`), has one
memory of one page, and exports `check : [i32] → []`:

```wat
(func $check (param $h i32)
  (call $items (local.get $h) (i32.const 0))       ;; (ptr, len) at [0, 8)
  (if (i32.ne (i32.load offset=4 (i32.const 0)) (i32.const 2)) (then (return)))
  (call $accept (local.get $h)))
```

It accepts its argument when the returned list has two elements: its reader language is
included in `twoL`, the lists of two children, whatever the children are. The length is read by the
module from the memory the host wrote (`i32.load offset=4`), the same bytes the decoder of the
`items` reply reads (`Silmaril.Wasm.Game.HandleAccept.MemSound.itemsList`).

The admitted hosts (`itemsReply`): an answer keeps the code and the number of memories (and may
write any memory contents: that is how the list is returned), and returns no values.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Items

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- `[i32 i32] → []`. -/
def tyItems : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], []⟩⟩]⟩

/-- The body of `check`. -/
def itemsBody : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 0, .call ⟨0⟩,
   .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩,
   .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨1⟩]

/-- **The module.** -/
def itemsMod : Module where
  types := [tyItems, tyAcc]
  imports := [⟨"sexp", "items", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨1⟩, [], itemsBody⟩]
  exports := [⟨"check", .func ⟨2⟩⟩]

/-- The admitted host replies: they keep the code and return no values. -/
def itemsReply : UCall Nat → UReply → Prop := ShapedReply fun _ vs => vs = []

/-- **Lists of two children.** -/
def twoL : Set SymStrBytesSExp := {x | ∃ c₁ c₂, x = SExp.ofList [c₁, c₂]}

end Silmaril.Wasm.Game.HandleAccept.MemSound.Items
