module

public import Silmaril.Games.Abstract.HostRun.Defs
public import Silmaril.Wasm.Execution.Core.Step

/-!
# Core 3.0 host calls as a relational host (stage H2, first step)

A Core 3.0 host semantics `host : HostSemantics H` is a relation. For a host
function `h`, a store `s` and arguments `vs`, it allows the outcomes
`.returned s' r` and `.diverged`, possibly several, possibly none. This module
reads it as a `HostRel` of `Silmaril.Games.Abstract.HostRun`:

* `wasmHostSig H`: a host import call is a triple (host function, store,
  arguments), answered by (store, result);
* `coreHostRel host`: an answer `(s', r)` is allowed when `host` returns it, and
  divergence when `host` diverges. A call with no outcome is `blocked`.

The store is part of the call and of the answer, so a log of host answers
fixes every store update the host makes.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Host import calls: host function, store and arguments, answered by store and result. -/
abbrev wasmHostSig (H : Type) : Sig.{0} := ⟨H × Store H × List Val, fun _ => Store H × Result⟩

/-- **A Core 3.0 host semantics as a relational host.** -/
def coreHostRel (host : HostSemantics H) : HostRel (wasmHostSig H) := fun m o =>
  match o with
  | .answer p => host m.1 m.2.1 m.2.2 (.returned p.1 p.2)
  | .diverge => host m.1 m.2.1 m.2.2 .diverged

end Silmaril.Wasm.Abstract
