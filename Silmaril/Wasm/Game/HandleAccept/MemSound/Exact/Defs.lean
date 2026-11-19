module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Defs
public import Silmaril.Semantics.Accept.Mixed.Chunk.Defs

/-!
# Exact pull-chunk echo: a writer and pull-chunk module relating input bytes to their atom

`Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix.blobEcho` reads a chunk, builds its byte atom and
reports it with `finish(n, h)`; against hosts that trap `blob` after answering `read`, a chunk
stays buffered and the next invocation's `finish` consumes stale bytes (`blobEcho_not_exact`).
`drainEcho z` first **drains** whatever an interrupted invocation may have left buffered, then
runs the body of `blobEcho`:

```wat
(func $run (local $n i32)
  (call $finish (i32.const 16) (i32.const z))   ;; drain: consume 16 buffered bytes, if there are
  (call $finish (i32.const 8) (i32.const z))    ;;        16; then 8, 4, 2, 1
  (call $finish (i32.const 4) (i32.const z))
  (call $finish (i32.const 2) (i32.const z))
  (call $finish (i32.const 1) (i32.const z))
  (local.set $n (call $read (i32.const 0) (i32.const 16)))          ;; a chunk at [0, n)
  (call $finish (local.get $n) (call $blob (i32.const 0) (local.get $n))))
```

`z` is the parser's failure sentinel (`PPolicy.sentinel`): a drain call `finish(k, z)` relates
nothing and consumes `k` buffered bytes when at least `k` are buffered. When fewer are buffered it
is an **overrun** (`Silmaril.Accept.Parse.PStep`): under the default `onOverrun = callTrap` (and
`ignore`) it relates nothing and leaves the cursor, so the drain consumes, in binary, exactly the
`L ≤ 31` bytes an earlier invocation left (`chunkStep`); under `sessionTrap` an overrun ends the
parsing session (no further pairs; soundness still holds, the relation may be empty); `ub` is
excluded. The module keeps no state between invocations (the admitted hosts may rewrite globals
and memory); the bound "at most 16 bytes buffered" is a property of every interrupted prefix: an
invocation drains to `0`, reads at most `16`, consumes them by `finish`, and any trap leaves at
most `16`.

## Ghost contract

`exactK z sent σ` (`Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.GContract`) has the chunk buffer
of the parsing session as ghost state (`mixUpd`: `chunkStep` on parsing events, writer events keep
it):

* `pre g o`: at most `16` bytes are buffered, and every `finish(n, h)` call has `h` the parser's
  sentinel `z`, or the writer's sentinel `sent`, or `n` buffered bytes whose byte atom `h` denotes
  in the writer store `σ`;
* `ans`: decoded writes agree with `σ` (`Silmaril.Accept.Mixed.WriteAgrees`);
* `reply`: `blobReply`, the admitted hosts of `blobEcho`, unchanged.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Exact

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost

/-! ## The chunk buffer -/

/-- The ghost update of memory mixed sessions: the chunk buffer moves on parsing events. -/
def mixUpd : List UInt8 → MixEv → List UInt8
  | b, .p e => chunkStep b e
  | b, .w _ => b

/-! ## The module -/

/-- `finish(k, z)`. -/
def drainCall (k z : BitVec 32) : List Instr := [.intConst .i32 k, .intConst .i32 z, .call ⟨2⟩]

/-- The body of `run`: the binary drain, then the body of `blobEcho`. -/
def drainBody (z : BitVec 32) : List Instr :=
  drainCall 16 z ++ drainCall 8 z ++ drainCall 4 z ++ drainCall 2 z ++ drainCall 1 z ++
    blobEchoBody

/-- **The module**, for the parser sentinel `z`: the imports, memory, types and export of
`blobEcho`, with the draining body. -/
def drainEcho (z : BitVec 32) : Module where
  types := [tySym, tyFin, tyRun]
  imports := [⟨"input", "read", .func ⟨0⟩⟩, ⟨"sexp", "blob", .func ⟨0⟩⟩,
    ⟨"input", "finish", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32], drainBody z⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-! ## The ghost contract -/

/-- **The ghost contract of `drainEcho z`** for the writer sentinel `sent` and the writer store
`σ`. -/
def exactK (z : BitVec 32) (sent : Option (BitVec 32))
    (σ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp) :
    GContract MixEv (List UInt8) where
  pre g o := g.length ≤ 16 ∧ ∀ n h, pullFinish {} o = some (.finish n h) →
    h = z ∨ sent = some h ∨ (n ≤ g.length ∧ σ h = some (bytesAtom (g.take n)))
  ans x := ∀ op args r, x = .w (.write op args r) → WriteAgrees (sexpW MemAtom) sent σ op args r
  reply := blobReply
  upd := mixUpd

/-! ## Scripted hosts -/

/-- **A scripted host**, counting the `read` calls it has answered: `finish` (host code `2`)
returns nothing; the `k`-th `read(0, 16)` (host code `0`) rewrites the store by `rd k` and
returns `2`; `blob` (host code `1`), called after `k` reads, answers `bl k` in the caller's
store. Other calls are not answered. -/
def deEnv (rd : Nat → Store Nat → Store Nat) (bl : Nat → Result) : SEnv UImp where
  S := Nat
  Ans k e a k' :=
    (e.target = 2 ∧ a = ⟨e.store, .values []⟩ ∧ k' = k) ∨
      (e.target = 0 ∧ e.args = [.i32 0, .i32 16] ∧ a = ⟨rd k e.store, .values [.i32 2]⟩ ∧
        k' = k + 1) ∨
      (e.target = 1 ∧ a = ⟨e.store, bl k⟩ ∧ k' = k)
  Div _ _ := False

/-- Every read writes `68 69`; every `blob` returns `q`. -/
def hiEnv (q : BitVec 32) : SEnv UImp := deEnv (fun _ => hiStore) (fun _ => .values [.i32 q])

/-- The first read writes `68 69`, later ones `69 68`; the first `blob` returns `q₁`, later ones
`q₂`. -/
def twoEnv (q₁ q₂ : BitVec 32) : SEnv UImp :=
  deEnv (fun k => if k = 0 then hiStore else ihStore)
    (fun k => if k ≤ 1 then .values [.i32 q₁] else .values [.i32 q₂])

/-- **The stale-chunk host of `blobEcho`, scripted for `drainEcho`**: the first read writes
`68 69` and the first `blob` traps; later reads write `69 68` and later `blob`s return `q`. -/
def trapEnv (q : BitVec 32) : SEnv UImp :=
  deEnv (fun k => if k = 0 then hiStore else ihStore)
    (fun k => if k ≤ 1 then .trap else .values [.i32 q])

end Silmaril.Wasm.Game.HandleAccept.MemSound.Exact
