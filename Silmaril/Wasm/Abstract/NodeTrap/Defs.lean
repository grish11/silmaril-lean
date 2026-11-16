module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Games.Abstract.SessionTrap.Defs

/-!
# Core 3.0 instance rounds abort on an import trap: definitions

An import call of a scalar Core 3.0 instance `I` is an operation of `I.E = ifaceSig I.imports`,
answered by an `Answer`: typed values, a trap, or an uncaught exception. `IsTrapA e v` says that
the answer `v` to the import call `e` is the trap `Answer.trap`; it is the trap predicate of
`SessionTrap.TrapAbortsRound` for the instance triple `instTripleS I P`. An uncaught exception
answer `Answer.throw a` is not a trap: it is thrown inside the instance, which may catch it.

Theorems in `Silmaril.Wasm.Abstract.NodeTrap.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.NodeTrap

open Silmaril.Wasm.Game

/-- **The trap answers of an import signature**: the answer `v` to `e` is a trap. -/
def IsTrapA {ts : List FnType} (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) : Prop :=
  v = Answer.trap

end Silmaril.Wasm.Abstract.NodeTrap
