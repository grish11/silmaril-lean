module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Defs

/-!
# A one-shot parser with a proved relation

`nzParse` (import `0 word : [i64] → [i32]`; export `0 parse : [i64] → [i32]`) answers
`parse(0)` with the sentinel `0` and `parse(x)`, `x ≠ 0`, with `word(x)`. Its parsing exports are
`nzIx` (only `parse`, one `i64` datum).

Parse specifications constrain the module's *answers* only: the writer import `word` is
unconstrained (`topISpec`), so nothing is known of the tree its handle denotes. What the module
guarantees is on the input: a non-sentinel answer is only given to a nonzero datum. Its relation
is `nzR`: the one-value inputs `[v]` with `v ≠ 0`, with any tree.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `[i64] → [i32]`. -/
def tyWord : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩

/-- The body of `parse`: the sentinel `0` on `0`, `word(x)` otherwise. -/
def nzBody : List Instr :=
  [.localGet ⟨0⟩, .intTestOp .i64 .eqz, .if_ .empty [.intConst .i32 0, .return_] [],
   .localGet ⟨0⟩, .call ⟨0⟩, .return_]

/-- **A one-shot parser of nonzero words.** -/
def nzParse : Module where
  types := [tyWord]
  imports := [⟨"sexp", "word", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], nzBody⟩]
  exports := [⟨"parse", .func ⟨1⟩⟩]

/-- Its parsing export. -/
def nzIx : ParseExports (BitVec 64) := {val := i64Val, parse := some 0}

/-- One nonzero word, with any tree. -/
def nzR (X : Type) : Set (List (BitVec 64) × X) := {q | ∃ v, q.1 = [v] ∧ v ≠ 0}

/-- The store invariant: the store's functions are those of the instantiated module (import
calls return the store unchanged and `nzParse` writes no store). -/
def nzInv (s : Store Nat) : Prop := s.funcs = (Verify.instOf nzParse).store.funcs

end Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers
