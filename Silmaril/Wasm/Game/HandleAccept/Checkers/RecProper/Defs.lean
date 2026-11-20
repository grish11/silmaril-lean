module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs

/-!
# A nested-list checker: recursive properness to depth two

`properCheck` (`Silmaril.Wasm.Game.HandleAccept.Checkers`) walks the `cdr` spine only, so it
accepts lists whose elements are dotted pairs (`dottedElem = ((() . 1))`). `recProperCheck`
also inspects every element: an element must be an atom, or a proper list **of atoms** (walked by
an inner loop; `nil` is the empty one). It is a Core 3.0 module over the cons reader API
(`consIx`: `0 kind`, `1 car`, `2 cdr`, `3 word`, `4 accept`), exporting `check : [i32] → []`,
built as `checker [i32, i32, i32] rpOuter`. Locals: `0` the argument `h`, `1` the outer
cursor `cur`, `2` a kind, `3` the element / inner cursor.

* `rpOuter`: `stepHead` (accept `h` when `cur` is nil, return unless it is a cons cell), then
  the element `car(cur)` into local `3`; an atom element advances `cur := cdr(cur)` and continues
  the outer loop (`br 1`); otherwise the inner loop runs on it.
* `rpInner`: on nil the element is finished: `cur := cdr(cur)` and continue the outer loop
  (`br 2`); a cons cell must have an atom `car` (else return), then `cdr` and continue; anything
  else returns.

**Language.** `nestL`: proper lists whose elements satisfy `NestElem` (an atom, or a proper
list of words `wordsL`). It lies strictly between `wordsL` and `recProperL` (`Thms`): this is a
**depth-bounded** check of recursive properness, not the full `recProperL`. Checking
`recProperL` itself needs unbounded storage (a stack of pending `cdr` handles, in linear memory
or through Wasm recursion), which the shared reader-checker proof rules do not cover.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-- `cur := cdr(cur)`. -/
def rpAdvance : List Instr := [.localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩]

/-- The inner loop over an element (local `3`): a proper list of atoms. -/
def rpInner : List Instr :=
  [.localGet ⟨3⟩, .call ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .intTestOp .i32 .eqz, .if_ .empty (rpAdvance ++ [.br ⟨2⟩]) [],
   .localGet ⟨2⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨3⟩, .call ⟨1⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne,
     .if_ .empty [.return_] [],
   .localGet ⟨3⟩, .call ⟨2⟩, .localSet ⟨3⟩, .br ⟨0⟩]

/-- The outer loop over the spine (local `1`). -/
def rpOuter : List Instr :=
  stepHead ++
  [.localGet ⟨1⟩, .call ⟨1⟩, .localSet ⟨3⟩,
   .localGet ⟨3⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .eq,
   .if_ .empty (rpAdvance ++ [.br ⟨1⟩]) [],
   .loop .empty rpInner]

/-- **Proper lists whose elements are atoms or proper lists of atoms.** -/
def recProperCheck : Module := checker [.i32, .i32, .i32] rpOuter

/-- The elements `recProperCheck` allows: atoms and proper lists of words. -/
def NestElem (x : SExp2 (BitVec 64)) : Prop := (∃ w, x = .atom w) ∨ x ∈ wordsL

/-- Proper lists whose elements satisfy `NestElem`. -/
inductive NestList : SExp2 (BitVec 64) → Prop where
  | nil : NestList .nil
  | cons {x y : SExp2 (BitVec 64)} : NestElem x → NestList y → NestList (.cons x y)

/-- The language of `recProperCheck`: recursively proper lists of nesting depth at most two
whose innermost elements are words. -/
def nestL : Set (SExp2 (BitVec 64)) := {x | NestList x}

/-- The nested list `((1 2) 3)`. -/
def nested123 : SExp2 (BitVec 64) := SExp2.ofList [SExp2.ofAtoms [1, 2], .atom 3]

end Silmaril.Wasm.Game.HandleAccept.Checkers
