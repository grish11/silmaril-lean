module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Examples

/-!
# A writer module with a proved language

`twoWords` (imports, by index `twoIx`: `0 nil : [] → [i32]`, `1 cons : [i32 i32] → [i32]`,
`2 word : [i64] → [i32]`, `3 accept : [i32] → []`; export `run : [i64] → []`) builds
`cons(word(x), cons(word(x + 1), nil()))` and accepts it: the two-element list `(x x+1)` of
`i64` words (`x + 1` wraps). Its language is `twoWordsL`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Builders

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples

/-- The body of `run`. -/
def twoBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩,
   .localGet ⟨0⟩, .intConst .i64 1, .intBinOp .i64 .add, .call ⟨2⟩,
   .call ⟨0⟩, .call ⟨1⟩, .call ⟨1⟩, .call ⟨3⟩]

/-- **Accept `(x x+1)`.** -/
def twoWords : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  funcs := [⟨⟨4⟩, [], twoBody⟩]
  exports := [⟨"run", .func ⟨4⟩⟩]

/-- Its imports as cons writer imports. -/
def twoIx : ConsWImports := ⟨0, 1, 2, 3, none⟩

/-- The two-element lists of consecutive words. -/
def twoWordsL : Set (SExp2 (BitVec 64)) := {t | ∃ x : BitVec 64, t = SExp2.ofAtoms [x, x + 1]}

end Silmaril.Wasm.Game.HandleAccept.Writers.Builders
