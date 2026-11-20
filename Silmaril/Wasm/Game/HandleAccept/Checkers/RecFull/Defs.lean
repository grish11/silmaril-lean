module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs

/-!
# A full recursive-properness checker: Wasm recursion over the elements

`recProperCheck` (`Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper`) checks recursive
properness only to nesting depth two. `recFullCheck` checks the whole of `recProperL`, at every
depth, by **Wasm function recursion**: its exported function `check(h)` (function `5`, type
`[i32] → []`, over the cons reader imports `consIx`: `0 kind`, `1 car`, `2 cdr`, `3 word`,
`4 accept`) walks the `cdr` spine of `h` and calls **itself** (`call 5`) on every element that
is not an atom. It is built as `checker [i32, i32, i32] (rfHead ++ rfElem)`; locals: `0` the
argument `h`, `1` the spine cursor `cur`, `2` a kind, `3` the element.

* `rfHead`: `kind(cur)`; on nil, `accept(h)` and return; on anything but a cons cell, **trap**
  (`unreachable`). Failure traps instead of returning so that a recursive call that returns
  normally certifies its argument: the caller continues only after a successful check.
* `rfElem`: the element `car(cur)`; unless it is an atom, `check` it recursively (which accepts
  it, as a recursively proper list, and returns, or traps); then `cur := cdr(cur)` and continue.

A call `check(h)` therefore accepts `h` and every non-atom element of it, recursively, exactly
when `h` is a recursively proper list; a non-proper subtree traps the whole export call before
`h` is accepted. The recursion depth is unbounded in the semantics (the profiles of the logic
impose no call-stack bound; an implementation's stack exhaustion is a trap, which is sound).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-- `kind(cur)` into local 2; accept the argument on nil; trap unless cons. -/
def rfHead : List Instr :=
  [.localGet ⟨1⟩, .call ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .intTestOp .i32 .eqz, .if_ .empty [.localGet ⟨0⟩, .call ⟨4⟩, .return_] [],
   .localGet ⟨2⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.unreachable] []]

/-- The element `car(cur)` (local 3) is checked recursively unless it is an atom; then
`cur := cdr(cur)`, next iteration. -/
def rfElem : List Instr :=
  [.localGet ⟨1⟩, .call ⟨1⟩, .localSet ⟨3⟩,
   .localGet ⟨3⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne,
   .if_ .empty [.localGet ⟨3⟩, .call ⟨5⟩] [],
   .localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩]

/-- **Recursively proper lists, at every depth**, by Wasm recursion. -/
def recFullCheck : Module := checker [.i32, .i32, .i32] (rfHead ++ rfElem)

/-- `(((1)))`: recursively proper, nested three deep. -/
def deep1 : SExp2 (BitVec 64) := SExp2.ofList [SExp2.ofList [SExp2.ofAtoms [1]]]

end Silmaril.Wasm.Game.HandleAccept.Checkers
