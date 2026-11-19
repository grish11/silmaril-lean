module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Thms

/-!
# The n-ary reader API: an example module

`pairCheck` (imports `0 kind`, `1 count : [i32] → [i32]`, `2 child : [i32 i32] → [i32]`,
`3 word : [i32] → [i64]`, `4 accept : [i32] → []`; export `check : [i32] → []`) accepts its
argument when `kind` answers list and `count` answers two. It validates and instantiates
(`pairCheck_instance`). Its intended language is the two-element lists `pairL`; by
`sexpLang_sound_of_forall`, `moduleSExpLang P pairCheck pairIx .trap oa Envs ⊆ pairL` follows
from its Hoare-logic obligation `GameSat … (sexpISpec pairIx ρ pairL)`, proved in
`Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Thms` (`pairCheck_sat`, `pairCheck_sound`).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Nary.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-- `[i32] → [i32]`. -/
def tyQ : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyC : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i32] → [i64]`. -/
def tyW : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i64]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩

/-- The n-ary reader imports. -/
def sxImports : List Import :=
  [⟨"sexp", "kind", .func ⟨0⟩⟩, ⟨"sexp", "count", .func ⟨0⟩⟩, ⟨"sexp", "child", .func ⟨1⟩⟩,
   ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]

/-- Their indices. -/
def pairIx : SxRImports := ⟨0, 1, 2, 3, 4⟩

/-- **Accept two-element lists.** -/
def pairCheck : Module where
  types := [tyQ, tyC, tyW, tyA]
  imports := sxImports
  funcs := [⟨⟨3⟩, [],
    [.localGet ⟨0⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
     .localGet ⟨0⟩, .call ⟨1⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
     .localGet ⟨0⟩, .call ⟨4⟩]⟩]
  exports := [⟨"check", .func ⟨5⟩⟩]

/-- Two-element lists. -/
def pairL : Set (SExp (BitVec 64)) := {x | ∃ a b, x = SExp.ofList [a, b]}

theorem pairCheck_instance : (Verify.instance? pairCheck).isSome = true := by decide +kernel

end Silmaril.Wasm.Game.HandleAccept.Nary.Examples
