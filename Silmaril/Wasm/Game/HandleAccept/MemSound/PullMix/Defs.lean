module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pull.Defs
public import Silmaril.Semantics.Accept.Mixed.Defs

/-!
# Memory mixed sessions: memory writers and pull-style chunks in one traced session

`Silmaril.Accept.Mixed` combines a writer (`WEv`) with a parsing session (`PEv`) and resolves
every handle a parsing event returns in the **current writer store** (`mixedRel`). Here both
sides are decoded from the memory-observing traced sessions of
`Silmaril.Wasm.Game.IOAccept` (`TSession`):

* writer events by the memory writer decoders of `Silmaril.Wasm.Game.HandleAccept.Memory`
  (`memWrite` at answers: `symbol`, `string`, `blob`, `sexp`; `memAccept` at calls);
* parsing events by the pull-style decoders of `Silmaril.Wasm.Game.HandleAccept.MemSound.Pull`
  (`pullRead` at answers: `read(buf, cap)` answered with `n` is `feed` of the `n` bytes at
  `buf` in the memory after the answer; `pullFinish` at calls: `finish(used, tree)`).

`mixCall`/`mixAnswer` try the writer decoder first, then the pull decoder (with the default
import names they never both apply). Export invocations are the writer's `enter`
(`mixTraces`), so a call-local writer trap ends at the next invocation. `memMixedRel` is the
mixed input/tree relation (`Silmaril.Accept.Mixed.mixedRel`, store semantics) of those traces:
byte inputs, trees over `MemAtom`.

## The example `blobEcho`

`blobEcho` imports `input.read : [i32 i32] → [i32]` (import `0`), `sexp.blob : [i32 i32] → [i32]`
(import `1`) and `input.finish : [i32 i32] → []` (import `2`), has one memory of one page and
exports `run : [] → []` with one `i32` local:

```wat
(func $run (local $n i32)
  (local.set $n (call $read (i32.const 0) (i32.const 16)))      ;; a chunk at [0, n)
  (call $finish (local.get $n)                                   ;; report n bytes ...
    (call $blob (i32.const 0) (local.get $n))))                  ;; ... as the byte atom
```

It reads one chunk, builds the byte-string atom of the bytes it read, and reports that the
`n` bytes read parse to that atom.

The admitted hosts (`blobReply`) keep the code (`KeepsCode`), never shrink memory `0`
(`MemGrows`: Wasm hosts can grow memories, not shrink them), may rewrite its contents, may trap
or throw, and when they return values: `read` returns one `i32` not larger than its `cap`
argument, `blob` one `i32`, `finish` nothing.

**The stale-chunk hazard.** The chunk buffer of the parsing session persists across export
invocations (as the cursor semantics of `Silmaril.Accept.Parse` intends: unconsumed input stays
buffered). If a host traps the `blob` call after answering `read`, the invocation ends with the
chunk buffered and not consumed; the next invocation's `finish(n, h)` consumes the **old**
bytes, while `h` denotes the atom of the **new** chunk. `Thms.blobEcho_stale` exhibits the
resulting pair. Exact input/tree correctness of `blobEcho` therefore does not hold for all
admitted hosts; what holds for all of them is the length relation (`Thms.blobEcho_sound`).

`blobEnv q` is a concrete host: `read(0, 16)` writes `68 69` at `0` and returns `2`; `blob`
returns `q` in the caller's store; `finish` returns nothing. `staleEnv q` is the admitted host of
the hazard: it traps the first `blob` call, and in the second invocation `read` writes `69 68`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pull

/-! ## Decoders -/

/-- Events of memory mixed sessions: memory writer events and byte parsing events. -/
abbrev MixEv := MEv (SxOp MemAtom) UInt8 (BitVec 32)

/-- The event decoded at a call: an accept, else a finish. -/
def mixCall (ix : MemImports) (px : PullImports) (o : Callout) : Option MixEv :=
  match memAccept ix o with
  | some e => some (.w e)
  | none => (pullFinish px o).map .p

/-- The event decoded at an answer: a write, else a chunk. -/
def mixAnswer (ix : MemImports) (px : PullImports) (o : Callout) (w : HostReply) :
    Option MixEv :=
  match memWrite ix o w with
  | some e => some (.w e)
  | none => (pullRead px o w).map .p

/-- The roles of memory mixed sessions. -/
def mixRoles (ix : MemImports) (px : PullImports) : Roles Unit MixEv Unit Unit where
  callIn := mixCall ix px
  answerIn := mixAnswer ix px

/-- **The mixed traces of a module**: decoded inputs in order, export invocations as the
writer's `enter`. -/
def mixTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : MemImports) (px : PullImports) : Set (List MixEv) :=
  inputsOf (some (.w .enter)) '' tagTraces P Envs memIdx m (mixRoles ix px)

/-- **The mixed input/tree relation of a module** (store semantics): returned handles resolve in
the store of the trees the module wrote through memory. -/
def memMixedRel (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : MemImports) (px : PullImports) (pol : Policy (BitVec 32))
    (ppol : PPolicy (BitVec 32)) : Set (List UInt8 × SymStrBytesSExp) :=
  mixedRel (sexpW MemAtom) pol ppol (mixTraces P Envs memIdx m ix px)

/-! ## The example -/

/-- The body of `run`. -/
def blobEchoBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 16, .call ⟨0⟩, .localSet ⟨0⟩,
   .localGet ⟨0⟩, .intConst .i32 0, .localGet ⟨0⟩, .call ⟨1⟩, .call ⟨2⟩]

/-- **The module.** -/
def blobEcho : Module where
  types := [tySym, tyFin, tyRun]
  imports := [⟨"input", "read", .func ⟨0⟩⟩, ⟨"sexp", "blob", .func ⟨0⟩⟩,
    ⟨"input", "finish", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32], blobEchoBody⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Memory `0` is not shrunk. -/
def MemGrows (s s' : Store Nat) : Prop :=
  ∀ mi, s.mems[0]? = some mi → ∃ mi', s'.mems[0]? = some mi' ∧ mi.bytes.size ≤ mi'.bytes.size

/-- The admitted replies: the code is kept, memory `0` is not shrunk; `read` (host code `0`)
returns one `i32` not larger than its `cap` argument, `blob` (host code `1`) one `i32`, `finish`
(host code `2`) nothing. Traps and exceptions are allowed. -/
def blobReply (e : UCall Nat) (a : UReply) : Prop :=
  KeepsCode e.store a.store ∧ MemGrows e.store a.store ∧ ∀ vs, a.result = .values vs →
    (e.target = 0 → ∃ n, vs = [.i32 n] ∧ ∀ p c, e.args = [.i32 p, .i32 c] → n.toNat ≤ c.toNat) ∧
    (e.target = 1 → ∃ h, vs = [.i32 h]) ∧ (e.target = 2 → vs = [])

/-- The byte-string atom of `bs`. -/
def bytesAtom (bs : List UInt8) : SymStrBytesSExp := .atom ⟨.bytes, by decide, bs⟩

/-- **The length relation**: at most `16` input bytes, related to a byte atom of the same
length. Every pair of `blobEcho` is in it (`Thms.blobEcho_len`). -/
def lenRel : Set (List UInt8 × SymStrBytesSExp) :=
  {q | q.1.length ≤ 16 ∧ ∃ c : List UInt8, c.length = q.1.length ∧ q.2 = bytesAtom c}

/-- **The exact relation**: the input bytes related to their byte atom. -/
def exactRel : Set (List UInt8 × SymStrBytesSExp) := {q | q.2 = bytesAtom q.1}

/-- **A concrete host**: `read(0, 16)` writes `68 69` at `0` and returns `2`; `blob` returns `q`;
`finish` returns nothing; other calls are not answered. -/
def blobEnv (q : BitVec 32) : SEnv UImp where
  S := Unit
  Ans _ e a _ :=
    (e.target = 0 ∧ e.args = [.i32 0, .i32 16] ∧ a = ⟨hiStore e.store, .values [.i32 2]⟩) ∨
      (e.target = 1 ∧ a = ⟨e.store, .values [.i32 q]⟩) ∨
      (e.target = 2 ∧ a = ⟨e.store, .values []⟩)
  Div _ _ := False

/-- The store after the host wrote `69 68` at `[0, 2)` of memory `0` (unchanged if it cannot). -/
def ihStore (s : Store Nat) : Store Nat :=
  ((s.mems[0]?).bind fun mi =>
    (Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
      ((0x6869 : BitVec 32).setWidth _)).map fun b => s.setMem 0 { mi with bytes := b }).getD s

/-- **A host that traps one `blob` call**, counting its answers: the first `read(0, 16)` writes
`68 69` and returns `2`, the first `blob` traps; the second `read(0, 16)` writes `69 68` and
returns `2`, the second `blob` returns `q`, and `finish` returns nothing. -/
def staleEnv (q : BitVec 32) : SEnv UImp where
  S := Nat
  Ans k e a k' := k' = k + 1 ∧
    ((k = 0 ∧ e.target = 0 ∧ e.args = [.i32 0, .i32 16] ∧
        a = ⟨hiStore e.store, .values [.i32 2]⟩) ∨
      (k = 1 ∧ e.target = 1 ∧ a = ⟨e.store, .trap⟩) ∨
      (k = 2 ∧ e.target = 0 ∧ e.args = [.i32 0, .i32 16] ∧
        a = ⟨ihStore e.store, .values [.i32 2]⟩) ∨
      (k = 3 ∧ e.target = 1 ∧ a = ⟨e.store, .values [.i32 q]⟩) ∨
      (k = 4 ∧ e.target = 2 ∧ a = ⟨e.store, .values []⟩))
  Div _ _ := False

end Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix
