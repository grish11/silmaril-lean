module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Defs

/-!
# A streaming parser keeping its stack in globals

`stackParse` imports the cons writer API by the indices of `twoIx` (`0 nil : [] → [i32]`,
`1 cons : [i32 i32] → [i32]`, `2 word : [i64] → [i32]`, `3 accept : [i32] → []`, unused), has
two mutable `i32` globals, a flag `0` and a handle `1` (both initially `0`), and exports

* `0 append : [i64] → []`: if the flag is clear, `1 := nil()` and the flag is set; then
  `1 := cons(word(x), 1)`;
* `1 done : [] → [i32]`: if the flag is clear, `1 := nil()` and the flag is set; then it clears
  the flag and returns the handle `1`.

So `done()` returns the list of the values appended since the last `done`, **most recent
first**: after `append(x₁) … append(xₙ)` it builds `(xₙ … x₁)`, and an empty stream gives `()`.
The module keeps one handle between export calls: the list is built incrementally, so no
memory is needed.

* `stackPix`: the parsing exports (`append` export `0`, `done` export `1`, `i64` data);
* `stackR`: the intended relation, `(vs, SExp2.ofAtoms vs.reverse)`;
* `StackRep ρ g s fl acc` and the store invariant `stackInv ρ g s`: the flag is `fl`, the
  handle `acc`; a clear flag means the pending buffer `g` is empty, a set flag that `acc`
  denotes in `ρ` the list of `g` reversed (and the store's functions are those of the
  instance).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples Silmaril.Wasm.Game.HandleAccept.Parsing

/-- `if flag = 0 then (handle := nil(); flag := 1)`. -/
def prelude : List Instr :=
  [.globalGet ⟨0⟩, .intTestOp .i32 .eqz,
   .if_ .empty [.call ⟨0⟩, .globalSet ⟨1⟩, .intConst .i32 1, .globalSet ⟨0⟩] []]

/-- The body of `append(x)`. -/
def appendBody : List Instr :=
  prelude ++ [.localGet ⟨0⟩, .call ⟨2⟩, .globalGet ⟨1⟩, .call ⟨1⟩, .globalSet ⟨1⟩, .return_]

/-- The body of `done()`. -/
def doneBody : List Instr :=
  prelude ++ [.globalGet ⟨1⟩, .intConst .i32 0, .globalSet ⟨0⟩, .return_]

/-- A mutable `i32` global, initially `0`. -/
def var0 : Global := ⟨⟨.var, .num (.int .i32)⟩, [.intConst .i32 0]⟩

/-- **A streaming parser returning the reversed list of the appended values.** -/
def stackParse : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  globals := [var0, var0]
  funcs := [⟨⟨4⟩, [], appendBody⟩, ⟨⟨0⟩, [], doneBody⟩]
  exports := [⟨"append", .func ⟨4⟩⟩, ⟨"done", .func ⟨5⟩⟩]

/-- Its parsing exports. -/
def stackPix : ParseExports (BitVec 64) := {val := i64Val, append := some 0, done := some 1}

/-- **The relation of `stackParse`**: the appended values and their list, reversed. -/
def stackR : Set (List (BitVec 64) × SExp2 (BitVec 64)) :=
  {q | q.2 = SExp2.ofAtoms q.1.reverse}

/-- The globals represent the pending buffer `g`: flag `fl`, handle `acc`. -/
def StackRep (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (g : List (BitVec 64)) (s : Store Nat)
    (fl acc : BitVec 32) : Prop :=
  gval s 0 = some (.i32 fl) ∧ gval s 1 = some (.i32 acc) ∧ (fl = 0 → g = []) ∧
    (fl ≠ 0 → ρ acc = some (SExp2.ofAtoms g.reverse))

/-- **The store invariant**: the store represents the pending buffer `g`. -/
def stackInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (g : List (BitVec 64))
    (s : Store Nat) : Prop :=
  s.funcs = (Verify.instOf stackParse).store.funcs ∧ ∃ fl acc, StackRep ρ g s fl acc

end Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
