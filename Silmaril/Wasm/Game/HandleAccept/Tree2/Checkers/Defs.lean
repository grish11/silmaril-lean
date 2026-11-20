module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs

/-!
# An executable reader checker over the binary-tree API

`combCheck` (a Core 3.0 module as a Lean AST literal) inspects a binary tree through the reader
imports, by index (`combIx`): `0 isAtom : [i32] → [i32]` (`0` pair, `1` atom),
`1 left`, `2 right : [i32] → [i32]`, `3 word : [i32] → [i64]`, `4 accept : [i32] → []`. It
exports `check : [i32] → []`: from `cur := h`, it accepts `h` when `cur` is an atom, returns
unless `cur` is a pair whose left half is an atom, and otherwise continues with
`cur := right(cur)`. Language `combL`: **right combs of words**,
`cons (atom w₁) (cons (atom w₂) … (atom w))`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
open Silmaril.Wasm.Game.HandleAccept.Checkers (tyQ tyW tyA)

/-- The binary-tree reader imports. -/
def t2Imports : List Import :=
  [⟨"tree", "isAtom", .func ⟨0⟩⟩, ⟨"tree", "left", .func ⟨0⟩⟩, ⟨"tree", "right", .func ⟨0⟩⟩,
   ⟨"tree", "word", .func ⟨1⟩⟩, ⟨"tree", "accept", .func ⟨2⟩⟩]

/-- Their indices. -/
def combIx : T2RImports := ⟨0, 1, 2, 3, 4⟩

/-- The loop body: locals `[h, cur, k]`. -/
def combLoop : List Instr :=
  [.localGet ⟨1⟩, .call ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .intConst .i32 1, .intRelOp .i32 .ne, .intTestOp .i32 .eqz,
   .if_ .empty [.localGet ⟨0⟩, .call ⟨4⟩, .return_] [],
   .localGet ⟨2⟩, .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨1⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne,
   .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩]

/-- **Right combs of words.** -/
def combCheck : Module where
  types := [tyQ, tyW, tyA]
  imports := t2Imports
  funcs := [⟨⟨2⟩, [.i32, .i32], [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty combLoop]⟩]
  exports := [⟨"check", .func ⟨5⟩⟩]

/-- The right comb of the words `ws` ending in the atom `w`. -/
def comb (ws : List (BitVec 64)) (w : BitVec 64) : Tree2 (BitVec 64) :=
  ws.foldr (fun a acc => .cons (.atom a) acc) (.atom w)

/-- Right combs of words. -/
def combL : Set (Tree2 (BitVec 64)) := {t | ∃ ws w, t = comb ws w}

end Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers
