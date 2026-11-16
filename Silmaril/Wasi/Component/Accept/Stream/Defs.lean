module

public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Semantics.Acceptors.Defs

/-! # Components as incremental byte acceptors

The one-call acceptors of `Silmaril.Wasi.Component.Accept` see a whole input at once. An
**incremental** component exports three functions, after the `process`/`query`/`reset`
protocol of `Silmaril.Semantics.Acceptors`:

* `process(chunk: list<u8>)` appends a chunk to the pending input;
* `query() -> bool` answers whether the pending input is accepted;
* `reset()` clears the pending input.

`StreamFns` names the three exports. A play of the component is read as a protocol trace:

* `events` is the protocol events of the export calls, as `Silmaril.Acceptor.Event`s over
  byte chunks;
* `answers` is the `bool` results of the `query` returns.

A `process` call whose argument does not decode as a `list<u8>` (`bytes?`) is dropped from
`events`. The specification then says nothing about such calls, and the component may do
anything with them.

`StreamCorrect fns σ L` asks that in every play the answers given so far are a prefix of the
specified answers `Silmaril.Acceptor.specObs L` of its events. It is the component form of
`Silmaril.Acceptor.CorrectInterleaved`. It is a **safety** property: a component that never
answers a query satisfies it. So it gives soundness and completeness of every answer that is
given, on inputs of any length, but it does not guarantee that an answer is given at all.
Strategies observe finite plays only, so answering is a liveness property, outside this model.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val)

/-- The exported functions of an incremental acceptor. -/
structure StreamFns where
  /-- `process(chunk: list<u8>)`. -/
  process : FnName
  /-- `query() -> bool`. -/
  query : FnName
  /-- `reset()`. -/
  reset : FnName

/-- The protocol event of an export call, if it is one. -/
def StreamFns.event (fns : StreamFns) : WEv → Option (Silmaril.Acceptor.Event (List UInt8))
  | .call g args =>
    if g = fns.process then (args1 bytes? args).map .process
    else if g = fns.query ∧ args = [] then some .query
    else if g = fns.reset ∧ args = [] then some .reset
    else none
  | _ => none

/-- The answer of a `query` return, if it is one. -/
def StreamFns.answer (fns : StreamFns) : WEv → Option Bool
  | .ret g [] (some [.bool b]) => if g = fns.query then some b else none
  | _ => none

/-- The protocol events of a trace. -/
def StreamFns.events (fns : StreamFns) (t : List WEv) : List (Silmaril.Acceptor.Event (List UInt8)) :=
  t.filterMap fns.event

/-- The answers given in a trace. -/
def StreamFns.answers (fns : StreamFns) (t : List WEv) : List Bool := t.filterMap fns.answer

/-- **The component answers every query it answers correctly**: in every play, the answers
so far are a prefix of the specified answers of the events. -/
def StreamCorrect {I X : Set FnName} (fns : StreamFns) (σ : Strategy (nsig I) (nsig X))
    (L : ByteLang) [DecidablePred (· ∈ L)] : Prop :=
  ∀ t ∈ Traces σ, fns.answers t <+: Silmaril.Acceptor.specObs L (fns.events t)

end Silmaril.Wasi.Accept
