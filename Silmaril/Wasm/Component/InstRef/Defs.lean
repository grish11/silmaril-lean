module

public import Silmaril.Wasm.Component.InstLitmus.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs

/-!
# Start functions: the instantiating IR against the reference machine, on litmus components

The instantiating denotation `Comp.denI (core3SemI P)` (`Silmaril.Wasm.Component.InstSem`,
`InstEngine`) and the reference machine (`Silmaril.Wasm.Component.Reference`, whose
`instantiateCore` runs a core module's start function, `runStart`) both run start functions at
instantiation. This module compares them on three single-module components with imports
(`Reference.SimpleI`), each read on the IR side through `SimpleI.toComp` (the IR component the
reference soundness theorems use: imports wired by `canon lower`, exports by `canon lift`) and on
the reference side through `SimpleI.toRef`:

* `callSI`: the module `callMod 1` (its start function calls the import `f` with `1`), importing
  `f: func(u32)`, no exports. The observable of its instantiation is the host call `f(1)`.
* `globSI`: the module `globMod` (its start function writes `42` into a global), exporting
  `get: func() -> u32`, which reads it. The observable is `get()` returning `42` after
  instantiation.
* `trapSI`: the module `trapMod` (its start function traps), exporting `get`. The observable is
  that instantiation fails.

On the reference side the host import is answered by a **logging host**: `unitG` answers every
call with no results, and `HLinked2.logG unitG` appends each answered call
`(host function, arguments, results)` to a log in the host state (`embL`). The log of a run
with no export calls is the list of host calls made during instantiation.

* `logOfCalls cs`: the log the IR's instantiation calls `cs` correspond to: an import call
  `(k, vals vs)` answered `vals ws` is the host event `(k, vs, ws)` (values through
  `toRefVal`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.InstRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstLitmus

/-- `callMod 1` with its import `f: func(u32)` and no exports. -/
def callSI : SimpleI := ⟨callMod 1, hostI, []⟩

/-- `globMod`, exporting `get: func() -> u32`. -/
def globSI : SimpleI := ⟨globMod, [], [⟨"get", ⟨[], [.u32]⟩, 0⟩]⟩

/-- `trapMod`, exporting `get: func() -> u32`. -/
def trapSI : SimpleI := ⟨trapMod, [], [⟨"get", ⟨[], [.u32]⟩, 0⟩]⟩

section Host

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The host answering every import call with no results. -/
def unitG : Unit → HostFuncId → List Value.Val → Option (List Value.Val × Unit) :=
  fun _ _ _ => some ([], ())

/-- **The logging embedder**: the specification embedder over `core3 neverFail` whose host
answers by `unitG` and logs each call (`HLinked2.logG`). -/
def embL : Embedder (core3 Silmaril.Wasm.SingleThreaded.neverFail)
    (Unit × List HLinked2.HostEvent) :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := fun _ _ => false,
    host := answerImplS (HLinked2.logG unitG) }

/-- The embedder over `core3 neverFail` without host functions. -/
def embT : Embedder (core3 Silmaril.Wasm.SingleThreaded.neverFail) Unit :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := fun _ _ => false,
    host := Canon.HostImpl.none }

end Host

/-- The host call `f(u32 1)` of `callSI`'s start function, at the component's interface. -/
def fV : sigU.Op := (0, .vals [.u32 1])

/-- The answer `()` of the host, as component values. -/
def unitV : Option Payload := some (.vals [])

/-- The host event of an answered import call of the IR, when both are component values. -/
def callEvent : (Σ _ : sigU.Op, Option Payload) → Option HLinked2.HostEvent
  | ⟨(k, .vals vs), some (.vals ws)⟩ => some (⟨k⟩, vs.map toRefVal, ws.map toRefVal)
  | _ => none

/-- **The log of the IR's instantiation calls**, as host events of the reference machine. -/
def logOfCalls (cs : List (Σ _ : sigU.Op, Option Payload)) : List HLinked2.HostEvent :=
  cs.filterMap callEvent

end Silmaril.Wasm.Component.InstRef
