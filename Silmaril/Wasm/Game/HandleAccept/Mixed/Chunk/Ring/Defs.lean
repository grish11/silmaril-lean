module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Defs

/-!
# A chunked parser with a ring buffer in linear memory

`Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.chunkTake` buffers at most two values, in two
globals. `chunkRingN cap` buffers **up to `cap`** `i64` values in a ring buffer in linear memory
and, like `chunkTake`, consumes **exactly what is asked for**; `chunkRing` is `chunkRingN 8`. The
proofs hold for every capacity `RingCap cap` (`0 < cap ≤ 8192`: the `8 * cap` bytes of the buffer
fit the one page, and no `i32` slot arithmetic overflows). Imports (by `twoIx`): `0 nil`,
`1 cons`, `2 word`, `3 accept` (unused). One memory page; two mutable `i32` globals, initially
`0`: the start slot `st` (global `0`) and the count `cnt` (global `1`). The buffered values are,
oldest first, the `i64`s at the byte addresses `8 * ((st + i) mod cap)` for `i < cnt`. Exports:

* `0 feed : [i64] → []`: if `cnt = cap`, loop forever (the buffer is full: the call never
  answers, so it buffers nothing and is observed as nothing); otherwise store `x` at
  `8 * ((st + cnt) mod cap)` and increment `cnt`;
* `1 finish : [i32] → [i32 i32]`: if `n > cnt` or `n = 0`, return `(0, nil())`; otherwise build,
  with a loop from the newest consumed value down to the oldest, the list
  `cons(word(v₀), … cons(word(vₙ₋₁), nil()))` of the oldest `n` values, set
  `st := (st + n) mod cap`, `cnt := cnt - n`, and return `(n, list)`; the other values stay
  buffered. (The loop leaves only by `return`; it is wrapped in a block followed by
  `unreachable` so that the body validates.)

* `ringPix`: the parsing exports (`feed` export `0`, `finish` export `1`, `i64` data);
* the relation is `Take.takeR`, `(vs, SExp2.ofAtoms vs)`;
* `slot cap st i`: the byte address of the `i`-th buffered value; `RingRep cap g s st cnt` and the
  store invariant `ringInv cap g s`: the globals hold `st < cap` and `cnt = |g| ≤ cap`, the store
  has one memory, and the `i64` loaded at `slot cap st i` is `g[i]` for every `i < |g|`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

/-- The capacity as an `i32` constant. -/
def capW (cap : Nat) : BitVec 32 := BitVec.ofNat 32 cap

/-- The capacities proved: at least one value, and the buffer (`8 * cap` bytes) within the one
memory page. -/
def RingCap (cap : Nat) : Prop := 0 < cap ∧ cap ≤ 8192

/-- `if cnt = cap then loop forever`. -/
def ringGuard (cap : Nat) : List Instr :=
  [.globalGet ⟨1⟩, .intConst .i32 (capW cap), .intRelOp .i32 .eq,
   .if_ .empty [.loop .empty [.br ⟨0⟩]] []]

/-- `8 * ((st + k) mod cap)`, with `k` on the stack below. -/
def slotAddr (cap : Nat) : List Instr :=
  [.intBinOp .i32 .add, .intConst .i32 (capW cap), .intBinOp .i32 (.rem .unsigned),
   .intConst .i32 8, .intBinOp .i32 .mul]

/-- The body of `feed(x)`. -/
def ringFeedBody (cap : Nat) : List Instr :=
  ringGuard cap ++
  [.globalGet ⟨0⟩, .globalGet ⟨1⟩] ++ slotAddr cap ++
  [.localGet ⟨0⟩, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .globalGet ⟨1⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨1⟩, .return_]

/-- The loop of `finish(n)`: locals `0 n`, `1 i` (values still to add), `2 acc` (the list of
the buffered values `i … n - 1`). -/
def ringLoopBody (cap : Nat) : List Instr :=
  [.localGet ⟨1⟩, .intTestOp .i32 .eqz,
   .if_ .empty [.globalGet ⟨0⟩, .localGet ⟨0⟩, .intBinOp .i32 .add, .intConst .i32 (capW cap),
     .intBinOp .i32 (.rem .unsigned), .globalSet ⟨0⟩,
     .globalGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i32 .sub, .globalSet ⟨1⟩,
     .localGet ⟨0⟩, .localGet ⟨2⟩, .return_] [],
   .localGet ⟨1⟩, .intConst .i32 (BitVec.allOnes 32), .intBinOp .i32 .add, .localSet ⟨1⟩,
   .globalGet ⟨0⟩, .localGet ⟨1⟩] ++ slotAddr cap ++
  [.intLoad .i64 none ⟨0⟩ ⟨0, 0⟩, .call ⟨2⟩, .localGet ⟨2⟩, .call ⟨1⟩, .localSet ⟨2⟩,
   .br ⟨0⟩]

/-- The body of `finish(n)`. -/
def ringFinBody (cap : Nat) : List Instr :=
  [.localGet ⟨0⟩, .globalGet ⟨1⟩, .intRelOp .i32 (.gt .unsigned),
   .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] [],
   .localGet ⟨0⟩, .intTestOp .i32 .eqz,
   .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] [],
   .call ⟨0⟩, .localSet ⟨2⟩, .localGet ⟨0⟩, .localSet ⟨1⟩,
   .block .empty [.loop .empty (ringLoopBody cap)], .unreachable]

/-- **A chunked parser with a ring buffer of `cap` values in linear memory.** -/
def chunkRingN (cap : Nat) : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun, tyFin2]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  globals := [var0, var0]
  funcs := [⟨⟨4⟩, [], ringFeedBody cap⟩, ⟨⟨5⟩, [.i32, .i32], ringFinBody cap⟩]
  exports := [⟨"feed", .func ⟨4⟩⟩, ⟨"finish", .func ⟨5⟩⟩]

/-- **The eight-value ring buffer.** -/
abbrev chunkRing : Module := chunkRingN 8

/-- Its parsing exports. -/
def ringPix : ParseExports (BitVec 64) := {val := i64Val, feed := some 0, finish := some 1}

/-- The byte address of the `i`-th buffered value from the start slot `st`. -/
def slot (cap st i : Nat) : Nat := 8 * ((st + i) % cap)

/-- The store represents the chunk buffer `g`: start slot `st`, count `cnt = |g|`, and the
`i64` at `slot cap st i` of memory `0` is `g[i]`. -/
def RingRep (cap : Nat) (g : List (BitVec 64)) (s : Store Nat) (st cnt : BitVec 32) : Prop :=
  gval s 0 = some (.i32 st) ∧ gval s 1 = some (.i32 cnt) ∧ st.toNat < cap ∧
    cnt.toNat = g.length ∧ g.length ≤ cap ∧ s.mems.length = 1 ∧
    ∀ i (hi : i < g.length), ∃ mi, s.mems[0]? = some mi ∧
      Execution.Memory.load mi.bytes (slot cap st.toNat i) 8 = some g[i]

/-- **The store invariant**: the store represents the chunk buffer `g`. -/
def ringInv (cap : Nat) (g : List (BitVec 64)) (s : Store Nat) : Prop :=
  s.funcs = (Verify.instOf (chunkRingN cap)).store.funcs ∧ ∃ st cnt, RingRep cap g s st cnt

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
