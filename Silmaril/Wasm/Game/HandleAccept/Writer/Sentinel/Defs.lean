module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Defs

/-!
# Writer modules that test for allocation failures

`twoWords` (`Silmaril.Wasm.Game.HandleAccept.Writers.Builders`) never tests the result of a
write, so it is proved sound only for policies without a failure sentinel. The modules here have
the same imports (`twoIx`: `0 nil`, `1 cons`, `2 word`, `3 accept`) and export
(`run : [i64] → []`) and build the same list `(x x+1)`, but every write result is stored in a
local and **tested against the sentinel before it is used**; on a failure `run` returns without
accepting anything (`guardRet`):

* `twoWordsZ`: the sentinel `0` (`i32.eqz`, test `isZ`);
* `twoWordsM`: the sentinel `-1 = 0xFFFFFFFF` (`i32.const -1; i32.eq`, test `isM`).

Both are `sentModule test` for a test fragment `test` leaving a non-zero `i32` exactly on the
sentinel. Locals: `1` the handle of `x`, `2` that of `x + 1`, `3` that of `nil`, `4` the list
under construction.

`WEv.writeOrEnter` classifies the events of a trace that cannot accept anything (writes and
export calls); the failure replays (`Examples`) use it.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples Silmaril.Wasm.Game.HandleAccept.Writers.Builders

/-- The failure test for the sentinel `0`. -/
def isZ : List Instr := [.intTestOp .i32 .eqz]

/-- The failure test for the sentinel `-1`. -/
def isM : List Instr := [.intConst .i32 (-1), .intRelOp .i32 .eq]

/-- `if test(local k) then return`. -/
def guardRet (test : List Instr) (k : LocalIdx) : List Instr :=
  .localGet k :: (test ++ [.if_ .empty [.return_] []])

/-- The body of `run`: each write result is guarded before use. -/
def sentBody (test : List Instr) : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩, .localSet ⟨1⟩] ++ guardRet test ⟨1⟩ ++
  [.localGet ⟨0⟩, .intConst .i64 1, .intBinOp .i64 .add, .call ⟨2⟩, .localSet ⟨2⟩] ++
    guardRet test ⟨2⟩ ++
  [.call ⟨0⟩, .localSet ⟨3⟩] ++ guardRet test ⟨3⟩ ++
  [.localGet ⟨2⟩, .localGet ⟨3⟩, .call ⟨1⟩, .localSet ⟨4⟩] ++ guardRet test ⟨4⟩ ++
  [.localGet ⟨1⟩, .localGet ⟨4⟩, .call ⟨1⟩, .localSet ⟨4⟩] ++ guardRet test ⟨4⟩ ++
  [.localGet ⟨4⟩, .call ⟨3⟩]

/-- The module of a failure test. -/
def sentModule (test : List Instr) : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  funcs := [⟨⟨4⟩, [.i32, .i32, .i32, .i32], sentBody test⟩]
  exports := [⟨"run", .func ⟨4⟩⟩]

/-- **Accept `(x x+1)`, testing every write against the sentinel `0`.** -/
def twoWordsZ : Module := sentModule isZ

/-- **Accept `(x x+1)`, testing every write against the sentinel `-1`.** -/
def twoWordsM : Module := sentModule isM

/-- Events that accept nothing in a run without undefined behaviour: writes and export calls. -/
def writeOrEnter {Op H : Type} : WEv Op H → Bool
  | .write _ _ _ => true
  | .enter => true
  | _ => false

/-- Some write of the trace returns `s`. -/
def retAny {Op : Type} (s : BitVec 32) : List (WEv Op (BitVec 32)) → Bool
  | [] => false
  | .write _ _ r :: es => r == s || retAny s es
  | _ :: es => retAny s es

end Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel
