module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Defs

/-!
# A chunked parser with partial consumption

`Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.chunkStack` consumes all or nothing. `chunkTake`
consumes **exactly what is asked for**: `finish(n)` with `n` values buffered (`0 < n`) consumes
the oldest `n` and returns their list, keeping the rest buffered; with fewer than `n` buffered it
consumes nothing. Imports (by `twoIx`): `0 nil`, `1 cons`, `2 word`, `3 accept` (unused). Three
mutable globals, initially `0`: two `i64` slots `0`, `1` and an `i32` count `2`; the buffer is
the first `count` slots (at most two values). Exports:

* `0 feed : [i64] → []`: if the count is `2`, loop forever (the buffer is full); otherwise store
  `x` in slot `count` and increment the count;
* `1 finish : [i32] → [i32 i32]`: if `n > count` or `n = 0`, return `(0, nil())`; if `n = 1`,
  return `(1, (slot₀))`, move slot `1` to slot `0` and decrement the count; otherwise (`n = 2 =
  count`) return `(2, (slot₀ slot₁))` and set the count to `0`.

So after `feed(7) feed(8)`, `finish(1)` consumes `[7]` (`used = 1`, strictly between `0` and the
`2` buffered values) and `8` stays buffered for the next `finish(1)`.

* `takePix`: the parsing exports (`feed` export `0`, `finish` export `1`, `i64` data);
* `takeR`: the intended relation, `(vs, SExp2.ofAtoms vs)` (in order);
* `TakeRep g s v₀ v₁ cnt` and the store invariant `takeInv g s`: the slots hold `v₀`, `v₁`, the
  count is `cnt ≤ 2`, and the chunk buffer `g` is `[v₀, v₁].take cnt` (and the store's functions
  are those of the instance). The invariant mentions no handle: the module keeps none between
  export calls.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

/-- A mutable `i64` global, initially `0`. -/
def var64 : Global := ⟨⟨.var, .num (.int .i64)⟩, [.intConst .i64 0]⟩

/-- `if count = 2 then loop forever`. -/
def capGuard : List Instr :=
  [.globalGet ⟨2⟩, .intConst .i32 2, .intRelOp .i32 .eq,
   .if_ .empty [.loop .empty [.br ⟨0⟩]] []]

/-- The body of `feed(x)`. -/
def takeFeedBody : List Instr :=
  capGuard ++
  [.globalGet ⟨2⟩, .intTestOp .i32 .eqz, .if_ .empty [.localGet ⟨0⟩, .globalSet ⟨0⟩] [],
   .globalGet ⟨2⟩, .intConst .i32 1, .intRelOp .i32 .eq,
   .if_ .empty [.localGet ⟨0⟩, .globalSet ⟨1⟩] [],
   .globalGet ⟨2⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨2⟩, .return_]

/-- The body of `finish(n)`. -/
def takeFinBody : List Instr :=
  [.localGet ⟨0⟩, .globalGet ⟨2⟩, .intRelOp .i32 (.gt .unsigned),
   .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] [],
   .localGet ⟨0⟩, .intTestOp .i32 .eqz,
   .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] [],
   .localGet ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .eq,
   .if_ .empty [.intConst .i32 1, .globalGet ⟨0⟩, .call ⟨2⟩, .call ⟨0⟩, .call ⟨1⟩,
     .globalGet ⟨1⟩, .globalSet ⟨0⟩, .globalGet ⟨2⟩, .intConst .i32 (BitVec.allOnes 32),
     .intBinOp .i32 .add, .globalSet ⟨2⟩, .return_] [],
   .intConst .i32 2, .globalGet ⟨0⟩, .call ⟨2⟩, .globalGet ⟨1⟩, .call ⟨2⟩, .call ⟨0⟩,
   .call ⟨1⟩, .call ⟨1⟩, .intConst .i32 0, .globalSet ⟨2⟩, .return_]

/-- **A chunked parser consuming exactly the requested values.** -/
def chunkTake : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun, tyFin2]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  globals := [var64, var64, var0]
  funcs := [⟨⟨4⟩, [], takeFeedBody⟩, ⟨⟨5⟩, [], takeFinBody⟩]
  exports := [⟨"feed", .func ⟨4⟩⟩, ⟨"finish", .func ⟨5⟩⟩]

/-- Its parsing exports. -/
def takePix : ParseExports (BitVec 64) := {val := i64Val, feed := some 0, finish := some 1}

/-- **The relation of `chunkTake`**: the consumed values and their list, in order. -/
def takeR : Set (List (BitVec 64) × SExp2 (BitVec 64)) :=
  {q | q.2 = SExp2.ofAtoms q.1}

/-- The globals represent the chunk buffer `g`: slots `v₀`, `v₁`, count `cnt`. -/
def TakeRep (g : List (BitVec 64)) (s : Store Nat) (v₀ v₁ : BitVec 64) (cnt : BitVec 32) :
    Prop :=
  gval s 0 = some (.i64 v₀) ∧ gval s 1 = some (.i64 v₁) ∧ gval s 2 = some (.i32 cnt) ∧
    cnt.toNat ≤ 2 ∧ g = [v₀, v₁].take cnt.toNat

/-- **The store invariant**: the store represents the chunk buffer `g`. -/
def takeInv (g : List (BitVec 64)) (s : Store Nat) : Prop :=
  s.funcs = (Verify.instOf chunkTake).store.funcs ∧ ∃ v₀ v₁ cnt, TakeRep g s v₀ v₁ cnt

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
