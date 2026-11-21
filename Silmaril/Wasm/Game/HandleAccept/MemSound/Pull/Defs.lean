module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs
public import Silmaril.Semantics.Accept.Parse.Defs

/-!
# Pull-style chunked input through linear memory

The parsing sessions of `Silmaril.Accept.Parse` feed input through exports
(`append(chunk)`, `done() -> (used, tree)`). Here the module **pulls** its input: it imports

* `input.read(buf, cap) -> i32`: the host writes some bytes at `[buf, buf + n)` of the module's
  memory and returns their count `n`. Decoded **at the answer** (`pullRead`, through
  `Silmaril.Wasm.Game.IOAccept.Roles.answerIn`) from the memory **after** the answer: the chunk
  event `PEv.feed bytes` with the `n` bytes at `buf` (no event when the reply is not one `i32`
  or the segment is out of bounds);
* `input.finish(used, tree)`: the module reports that the next `used` buffered bytes parse to
  the tree named by the handle `tree`. Decoded **at the call** (`pullFinish`): the cursor event
  `PEv.finish used tree` (`used` read by `usedOfI32`: no event when its sign bit is set).

`pullTraces` are the decoded inputs of the traced sessions, in order (export invocations carry
no parsing event), and `pullRel` is the parsing relation (`Silmaril.Accept.Parse.parseRel`)
of those traces: the chunks read are the buffered input, and each `finish` relates the `used`
bytes after the cursor to the tree of its handle in a fixed environment.

**The example** `echoMod` exports `run : [] → []`:

```wat
(func $run (call $finish (call $read (i32.const 0) (i32.const 16)) (i32.const 7)))
```

It reads one chunk of at most `16` bytes into `[0, 16)` and reports that the bytes read parse to
the tree of the handle `7`. The admitted hosts (`echoReply`) keep the code, may rewrite memory,
return one `i32` from `read` not larger than its `cap` argument (the import's contract), and
nothing from `finish`. `echoEnv` is a concrete such host: `read(0, 16)` writes `68 69` at `0`
and returns `2`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Pull

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## Decoders -/

/-- The named imports of pull-style input. -/
structure PullImports where
  read : String × String := ("input", "read")
  finish : String × String := ("input", "finish")

/-- Parsing events over bytes and `i32` handles. -/
abbrev PullEv := PEv UInt8 (BitVec 32)

/-- **`read(buf, cap)` answered with `n`**: the chunk of the `n` bytes at `buf` in the memory
after the answer. -/
def pullRead (ix : PullImports) (o : Callout) (w : HostReply) : Option PullEv :=
  if o.imp = ix.read then
    match o.args, replyI32 w with
    | [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, _⟩], some n =>
        (w.mem.bind fun mem => segOf mem p.toNat n.toNat).map .feed
    | _, _ => none
  else none

/-- **A call of `finish(used, tree)`.** -/
def pullFinish (ix : PullImports) (o : Callout) : Option PullEv :=
  if o.imp = ix.finish then
    match o.args with
    | [.num ⟨.int .i32, u⟩, .num ⟨.int .i32, h⟩] => (usedOfI32 u).map fun n => .finish n h
    | _ => none
  else none

/-- The roles of pull-style input: finishes at calls, chunks at answers. -/
def pullRoles (ix : PullImports) : Roles Unit PullEv Unit Unit where
  callIn := pullFinish ix
  answerIn := pullRead ix

/-- **The parsing traces of a module** through pull-style input. -/
def pullTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : PullImports) : Set (List PullEv) :=
  inputsOf none '' tagTraces P Envs memIdx m (pullRoles ix)

/-- **The input/tree relation of a module** through pull-style input, over the fixed
environments `Rhos`. -/
def pullRel {X : Type} (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : PullImports) (pol : PPolicy (BitVec 32))
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) : Set (List UInt8 × X) :=
  parseRel pol Rhos (pullTraces P Envs memIdx m ix)

/-! ## The example -/

/-- `[i32 i32] → []`. -/
def tyFin : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], []⟩⟩]⟩

/-- The body of `run`. -/
def echoBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 16, .call ⟨0⟩, .intConst .i32 7, .call ⟨1⟩]

/-- **The module.** -/
def echoMod : Module where
  types := [tySym, tyFin, tyRun]
  imports := [⟨"input", "read", .func ⟨0⟩⟩, ⟨"input", "finish", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], echoBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The admitted replies: the code is kept; `read` (host code `0`) returns one `i32` not larger
than its `cap` argument; `finish` (host code `1`) returns nothing. -/
def echoReply (e : UCall Nat) (a : UReply) : Prop :=
  KeepsCode e.store a.store ∧ ∀ vs, a.result = .values vs →
    (e.target = 0 → ∃ n, vs = [.i32 n] ∧ ∀ p c, e.args = [.i32 p, .i32 c] → n.toNat ≤ c.toNat) ∧
    (e.target = 1 → vs = [])

/-- The store after the host wrote `68 69` at `[0, 2)` of memory `0` (unchanged if it cannot). -/
def hiStore (s : Store Nat) : Store Nat :=
  ((s.mems[0]?).bind fun mi =>
    (Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
      ((0x6968 : BitVec 32).setWidth _)).map fun b => s.setMem 0 { mi with bytes := b }).getD s

/-- **A concrete host**: `read(0, 16)` writes `68 69` at `0` and returns `2`; `finish` returns
nothing; other calls are not answered. -/
def echoEnv : SEnv UImp where
  S := Unit
  Ans _ e a _ :=
    (e.target = 0 ∧ e.args = [.i32 0, .i32 16] ∧ a = ⟨hiStore e.store, .values [.i32 2]⟩) ∨
      (e.target = 1 ∧ a = ⟨e.store, .values []⟩)
  Div _ _ := False

end Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
