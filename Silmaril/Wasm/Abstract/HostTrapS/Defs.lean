module

public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Games.Abstract.SessionTrap.Defs
public import Silmaril.Games.Abstract.ModuleTrap.Defs

/-!
# Host traps end the native Wasm session round: definitions

The lower interface of the native session triple `sessionTripleXP` is the host calls
`wasmHostSig H`: a call `(hh, s, vs)` of the host function `hh` is answered by a store and a host
`Result`. The answer is a trap exactly when the result is `Result.trap`, whatever the store
(`IsHostTrap`); it is the only host answer that the open modules `wasmHOpenXP` and
`wasmHOpenXPS` turn into a trap end of the host function by itself (`resFlow .trap = .trap`).

* `IsHostTrap m n`: the host call `m` is answered by a trap, `n.2 = Result.trap`.
* `trapEndS H f e`: the end `e` of a function of the session shape `wasmHShapeS H` is a trap end
  (`SessionTrap.TrapEnd`: a trap keeping its store `.ret (.inr ()) s`, or a plain trap).
* `trapEndH H f e`: the end `e` of a function of the canonical shape `wasmHShape H` is `.trap`.

Theorems in `Silmaril.Wasm.Abstract.HostTrapS.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The host call is answered by a trap.** -/
def IsHostTrap (_ : (wasmHostSig H).Op) (n : Store H × Result) : Prop := n.2 = .trap

/-- **A trap end of the session shape**: a trap keeping its store, or a plain trap. -/
def trapEndS (H : Type) (_ : (wasmHShapeS H).F)
    (e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})) : Prop :=
  SessionTrap.TrapEnd e

/-- **A trap end of the canonical shape**: `End.trap`. -/
def trapEndH (H : Type) (_ : (wasmHShape H).F) (e : End (Store H) (List Val ⊕ Nat)) : Prop :=
  e = .trap

end Silmaril.Wasm.Abstract
