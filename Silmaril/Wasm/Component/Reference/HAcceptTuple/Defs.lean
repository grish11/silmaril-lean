module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs

/-!
# A `tuple<u8, u8>` acceptor as an `HLinked2`: definitions

The shape of `Silmaril.Wasi.Accept.Ref.Examples.tupleHiBytes` in the fragment of
`HLinkedSession`. A core module imports `env.accept : [i32, i32] → []`, and its export `run`
calls `accept(104, 105)`. The component lowers the host import
`accept: func(record<u8, u8>)` into it (the IR's tuples are records) and lifts `run: func()`.

* `tupleCore`: `(type (func (param i32 i32))) (type (func))
  (import "env" "accept" (func (type 0)))
  (func (type 1) i32.const 104 i32.const 105 call 0) (export "run" (func 1))`.
* `acceptTy`, `tupleI : SimpleI`: the importer.
* `tupleL : HLinked2`: `tupleI` with its only import a host import of the parent. There are no
  wired imports. The exporter is #697's `setGetS` (an `HLinked2` has one), which nothing calls.
* `acceptG`: the host's answers. Every call is answered with no results, and the state is
  unchanged.

This is a hand-written component of the `HLinked2` fragment that mirrors the core module and
the import type of `tupleHiBytes`. It is not decoded from those bytes: no map from bytes to
`HLinked2` exists (`docs/projects/component-caveats.md`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.HAcceptTuple

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetS unitFlat unitTy)

/-- The core module: `run` calls the import `env.accept` on `104, 105`. -/
def tupleCore : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  imports := [⟨"env", "accept", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 104, .intConst .i32 105, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The flat type `[i32, i32] -> []`. -/
abbrev pairFlat : CoreFuncTy := ⟨[.int .i32, .int .i32], []⟩

/-- `accept: func(record<u8, u8>)`. -/
abbrev acceptTy : FuncTy := ⟨[.record [.u8, .u8]], []⟩

/-- **The importer**: the host import `accept` lowered into `tupleCore`, whose `run` is lifted
as `run: func()`. -/
def tupleI : SimpleI :=
  ⟨⟨tupleCore, [("accept", pairFlat)], [("run", unitFlat)]⟩, [("accept", acceptTy)],
    [⟨"run", unitTy, 0⟩]⟩

/-- **The acceptor as an `HLinked2`**: `tupleI` with its import `accept` a host import of the
parent; no wired imports. -/
def tupleL : HLinked2 := ⟨setGetS, tupleI, [], [("accept", acceptTy)]⟩

/-- **The host's answers**: every host call is answered with no results, the state unchanged. -/
def acceptG : Unit → Silmaril.Wasm.Component.Runtime.HostFuncId →
    List Silmaril.Wasm.Component.Value.Val →
    Option (List Silmaril.Wasm.Component.Value.Val × Unit) :=
  fun s _ _ => some ([], s)

end Silmaril.Wasm.Component.Reference.HAcceptTuple
