module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Examples

/-!
# Executable reader checkers over the n-ary API

Two Core 3.0 modules (Lean AST literals) over the n-ary reader imports of
`Silmaril.Wasm.Game.HandleAccept.Nary.Examples` (by index `pairIx`: `0 kind : [i32] → [i32]`
(`0` atom, `1` list), `1 count : [i32] → [i32]`, `2 child : [i32 i32] → [i32]`,
`3 word : [i32] → [i64]`, `4 accept : [i32] → []`). Each exports `check : [i32] → []`.

* `wordsNCheck`: requires `h` to be a list (`kind`), reads its number of children `n`
  (`count`), and loops `i` from `0` to `n`: child `i` (`child(h, i)`) must be an atom
  (`kind` answers `0`); when `i = n` it accepts `h`. Language `wordsNL`: lists of words,
  `SExp.ofAtoms ws`.
* `sortedNCheck`: additionally reads the word of each child and requires it to be at least the
  previous one in the **signed** `i64` order (`i64.le_s`, `BitVec.sle`). Language
  `sortedNL ⊆ wordsNL`.

`count` and the index `i` are read **unsigned**: `i` stays below `n < 2 ^ 32`, so `i + 1` does
not wrap.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Nary.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Nary.Examples

/-- `h` (local 0) must be a list; its number of children goes to local 1. -/
def listHead : List Instr :=
  [.localGet ⟨0⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨1⟩, .localSet ⟨1⟩]

/-- Accept `h` when the index (local 2) reaches the count; otherwise child `i` (into local 3)
must be an atom. -/
def loopHead : List Instr :=
  [.localGet ⟨2⟩, .localGet ⟨1⟩, .intRelOp .i32 .eq,
   .if_ .empty [.localGet ⟨0⟩, .call ⟨4⟩, .return_] [],
   .localGet ⟨0⟩, .localGet ⟨2⟩, .call ⟨2⟩, .localSet ⟨3⟩,
   .localGet ⟨3⟩, .call ⟨0⟩, .if_ .empty [.return_] []]

/-- The word of the child (local 4) is at least the previous one (local 5) unless it is the
first (`i = 0`); then it becomes the previous one. -/
def elemSortedN : List Instr :=
  [.localGet ⟨3⟩, .call ⟨3⟩, .localSet ⟨4⟩,
   .localGet ⟨2⟩,
   .if_ .empty [.localGet ⟨5⟩, .localGet ⟨4⟩, .intRelOp .i64 (.le .signed), .intTestOp .i32 .eqz,
     .if_ .empty [.return_] []] [],
   .localGet ⟨4⟩, .localSet ⟨5⟩]

/-- `i := i + 1`, next iteration. -/
def loopTail : List Instr :=
  [.localGet ⟨2⟩, .intConst .i32 1, .intBinOp .i32 .add, .localSet ⟨2⟩, .br ⟨0⟩]

/-- A checker module from its locals and body. -/
def naryChecker (locals : List ValType) (body : List Instr) : Module where
  types := [tyQ, tyC, tyW, tyA]
  imports := sxImports
  funcs := [⟨⟨3⟩, locals, body⟩]
  exports := [⟨"check", .func ⟨5⟩⟩]

/-- **Lists of words.** -/
def wordsNCheck : Module :=
  naryChecker [.i32, .i32, .i32] (listHead ++ [.loop .empty (loopHead ++ loopTail)])

/-- **Sorted lists of words.** -/
def sortedNCheck : Module :=
  naryChecker [.i32, .i32, .i32, .i64, .i64]
    (listHead ++ [.loop .empty (loopHead ++ elemSortedN ++ loopTail)])

/-! ## Languages -/

/-- Lists of words. -/
def wordsNL : Set (SExp (BitVec 64)) := {x | ∃ ws, x = SExp.ofAtoms ws}

/-- Sorted lists of words (signed `i64` order). -/
def sortedNL : Set (SExp (BitVec 64)) :=
  {x | ∃ ws, x = SExp.ofAtoms ws ∧ ws.Pairwise fun a b => a.sle b = true}

end Silmaril.Wasm.Game.HandleAccept.Nary.Checkers
