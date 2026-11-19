module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Examples

/-!
# An executable reader checker over the AST API

A Core 3.0 module (a Lean AST literal) that inspects a tree of the arithmetic signature
`arithSig` (`num(s64)`, `add`, `neg`) through the AST reader API and calls `accept(h)` on the
handle `h` it was given when it passes. Imports, by index (`arithRIx`):

* `0 tag : [i32] → [i32, i64]`: a tag code (`0` num, `1` add, `2` neg; other codes do not
  decode) followed by the `s64` payload of `num` (ignored for the other tags);
* `1 count : [i32] → [i32]` (unsigned);
* `2 child : [i32 i32] → [i32]` (unsigned index);
* `3 accept : [i32] → []`.

It exports `check : [i32] → []`. `addCheck` accepts `h` when `h` is an `add` node with exactly
two children, each a `num` node without children. Language `addL`: the trees
`add(num a, num b)`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Ast.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Ast.Examples

/-- `[i32] → [i32, i64]`. -/
def tyT : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32, .i64]⟩⟩]⟩
/-- `[i32] → [i32]`. -/
def tyQ : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyC : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩

/-- The tag codes of `arithSig`: `0` num, `1` add, `2` neg. -/
def arithTagOfCode (c : BitVec 32) : Option ArithTag :=
  if c = 0 then some .num else if c = 1 then some .add else if c = 2 then some .neg else none

/-- The AST reader imports of the checker. -/
def arithRIx : AstRImports arithSig := ⟨0, arithTagOfCode, 1, 2, 3⟩

/-- Child `k` of the argument (into local 1) must be a `num` node without children. -/
def leafCheck (k : BitVec 32) : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 k, .call ⟨2⟩, .localSet ⟨1⟩,
   .localGet ⟨1⟩, .call ⟨0⟩, .drop, .intConst .i32 0, .intRelOp .i32 .ne,
   .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨1⟩, .intConst .i32 0, .intRelOp .i32 .ne, .if_ .empty [.return_] []]

/-- The body of the checker: an `add` node with two children, both leaves, is accepted. -/
def addBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨0⟩, .drop, .intConst .i32 1, .intRelOp .i32 .ne,
   .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨1⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] []] ++
  leafCheck 0 ++ leafCheck 1 ++ [.localGet ⟨0⟩, .call ⟨3⟩, .return_]

/-- **Accept `add(num a, num b)`.** -/
def addCheck : Module where
  types := [tyT, tyQ, tyC, tyA]
  imports := [⟨"ast", "tag", .func ⟨0⟩⟩, ⟨"ast", "count", .func ⟨1⟩⟩,
    ⟨"ast", "child", .func ⟨2⟩⟩, ⟨"ast", "accept", .func ⟨3⟩⟩]
  funcs := [⟨⟨3⟩, [.i32], addBody⟩]
  exports := [⟨"check", .func ⟨4⟩⟩]

/-- The leaf `num a`. -/
def numLeaf (a : Int64) : AST arithSig.toAstSig :=
  TExpr.ofList (⟨ArithTag.num, (a, ())⟩ : Σ t, arithSig.toAstSig.Arg t) []

/-- The trees `add(num a, num b)`. -/
def addL : Set (AST arithSig.toAstSig) :=
  {x | ∃ a b, x = TExpr.ofList (⟨ArithTag.add, ()⟩ : Σ t, arithSig.toAstSig.Arg t)
    [numLeaf a, numLeaf b]}

end Silmaril.Wasm.Game.HandleAccept.Ast.Checkers
