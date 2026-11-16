module

public import Silmaril.Wasi.Component.Accept.Stream.Defs
public import Silmaril.Semantics.Accept.Session.Defs

/-! # Incremental components as client sessions

The client view of an incremental component (`StreamFns`: exports `process(chunk: list<u8>)`,
`query() -> bool`, `reset()`), as a session of `Silmaril.Semantics.Accept.Session`
(`Silmaril.Accept.Call (List UInt8) (Option Bool)`):

* a call `process(chunk)` whose argument decodes as a `list<u8>` is `feed chunk`;
* a call `reset()` is `reset`;
* the return of a call `query()` is `query (some b)` when it returns `bool b`, and `query none`
  when it traps or returns anything else.

A query is recorded at its return, a feed or reset at its call. `sessionTraces fns σ` is the set
of sessions of the plays of `σ`. `Distinct` asks for three different function names.
`QueryTotal` asks that no completed query call of the component fail to return a `bool`. It is
needed only for sessions after a `reset` (`Silmaril.Wasi.Accept.feedsQuery_sound`), never for
fresh sessions.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-- The `bool` answer of a return, if it is one. -/
def answerOf : Option (List Val) → Option Bool
  | some [.bool b] => some b
  | _ => none

/-- The session call of a named event, if it is one. -/
def StreamFns.session (fns : StreamFns) : WEv → Option (Silmaril.Accept.Call (List UInt8) (Option Bool))
  | .call g args =>
    if g = fns.process then (args1 bytes? args).map .feed
    else if g = fns.reset ∧ args = [] then some .reset
    else none
  | .ret g args res => if g = fns.query ∧ args = [] then some (.query (answerOf res)) else none
  | _ => none

/-- The three functions are different. -/
def StreamFns.Distinct (fns : StreamFns) : Prop :=
  fns.process ≠ fns.query ∧ fns.process ≠ fns.reset ∧ fns.query ≠ fns.reset

/-- The client sessions of a component. -/
def sessionTraces {I X : Set FnName} (fns : StreamFns) (σ : Strategy (nsig I) (nsig X)) :
    Set (List (Silmaril.Accept.Call (List UInt8) (Option Bool))) :=
  (·.filterMap fns.session) '' Traces σ

/-- Every completed `query()` call returns a `bool`. -/
def QueryTotal {I X : Set FnName} (fns : StreamFns) (σ : Strategy (nsig I) (nsig X)) : Prop :=
  ∀ t ∈ sessionTraces fns σ, Silmaril.Accept.Call.query none ∉ t

end Silmaril.Wasi.Accept
