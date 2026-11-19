module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Defs

/-!
# A parser that builds its tree

`listParse` imports the cons writer API by the indices of `twoIx` (`0 nil : [] → [i32]`,
`1 cons : [i32 i32] → [i32]`, `2 word : [i64] → [i32]`, `3 accept : [i32] → []`, unused) and
exports `0 parse : [i64] → [i32]`:

* `parse(0)` answers the parsing sentinel `0`;
* `parse(x)`, `x ≠ 0`, builds `cons(word(x), nil())`, the one-element list `(x)`, and returns its
  handle.

Its parsing export is `listPix` (`parse` only, one `i64` datum), and its intended input/tree
relation is `listR`: the nonzero words `x` related to the list `(x)`, `SExp2.ofAtoms [x]`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Parser

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples Silmaril.Wasm.Game.HandleAccept.Parsing

/-- The body of `parse`: the sentinel `0` on `0`, `cons(word(x), nil())` otherwise. -/
def listBody : List Instr :=
  [.localGet ⟨0⟩, .intTestOp .i64 .eqz, .if_ .empty [.intConst .i32 0, .return_] [],
   .localGet ⟨0⟩, .call ⟨2⟩, .call ⟨0⟩, .call ⟨1⟩, .return_]

/-- **A one-shot parser building the one-element list `(x)`.** -/
def listParse : Module where
  types := [tyNil, tyCons, tyWord, tyA]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  funcs := [⟨⟨2⟩, [], listBody⟩]
  exports := [⟨"parse", .func ⟨4⟩⟩]

/-- Its parsing export. -/
def listPix : ParseExports (BitVec 64) := {val := i64Val, parse := some 0}

/-- **The relation of `listParse`**: a nonzero word and the one-element list of it. -/
def listR : Set (List (BitVec 64) × SExp2 (BitVec 64)) :=
  {q | ∃ x : BitVec 64, x ≠ 0 ∧ q = ([x], SExp2.ofAtoms [x])}

/-- The store invariant: the store's functions are those of the instantiated module. -/
def listInv (s : Store Nat) : Prop := s.funcs = (Verify.instOf listParse).store.funcs

end Silmaril.Wasm.Game.HandleAccept.Mixed.Parser
