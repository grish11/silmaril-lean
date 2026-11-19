module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs

/-!
# A module writing the symbol `hi` through linear memory

`hiMod` imports `sexp.symbol : [i32 i32] → [i32]` (import `0`) and `sexp.accept : [i32] → []`
(import `1`), has one memory of one page, and exports `run : [] → []`:

```wat
(func $run
  (i32.store16 (i32.const 0) (i32.const 0x6968))   ;; "hi" at [0, 2)
  (call $accept (call $symbol (i32.const 0) (i32.const 2))))
```

The bytes are written by the code, on every call, right before `symbol(0, 2)`, rather than by a
data segment: a host answering an earlier call may rewrite the module's memory (the contract
allows it), so a data segment written once at instantiation is not what a later call would read.

The admitted hosts (`hiReply`): an answer keeps the store's functions and the number of memories
(`KeepsCode`; memory contents may be rewritten arbitrarily), and returns one `i32` from `symbol`
(host code `0`) and nothing from `accept` (host code `1`), or traps, or throws. This is the
result typing every Core host meets on these imports (`UEnvOk`), stated without the store
typing.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory

/-- `[i32 i32] → [i32]`. -/
def tySym : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyAcc : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[] → []`. -/
def tyRun : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- The body of `run`. -/
def hiBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x6968, .intStore .i32 (some .i16) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩]

/-- **The module.** -/
def hiMod : Module where
  types := [tySym, tyAcc, tyRun]
  imports := [⟨"sexp", "symbol", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], hiBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The shape of the values returned by host code `k`: one `i32` from `symbol`, nothing from
`accept`. -/
def hiShape (k : Nat) (vs : List Val) : Prop :=
  (k = 0 → ∃ c, vs = [.i32 c]) ∧ (k = 1 → vs = [])

/-- The admitted host replies. -/
def hiReply : UCall Nat → UReply → Prop := ShapedReply hiShape

/-- The symbol `hi`. -/
def hiAtom : MemAtom := ⟨.symbol, by decide, "hi"⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
