module

public import Silmaril.Wasm.Abstract.HostTrapS.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Abstract.SessionTrap.Thms
import Silmaril.Proofs.Wasm.Abstract.HostTrapS.Basic

/-!
# Host traps end the native Wasm session round: theorems

Core Wasm traps the caller of a trapping callee at once, and no handler catches a trap. In the
native session triple `sessionTripleXP` over the host calls `wasmHostSig H`, a host trap is a host
call answered `(s', Result.trap)` (`IsHostTrap`), and:

* **Session runs** (`evalLXPS_trapLast`): in a run of `EvalLXPS`, a call answered by a trap is the
  last call, and the run ends in a trap flow (`callTrap`, `indTrap`, `refTrap`; a trap flow passes
  every block, loop, conditional and handler).
* **Open modules** (`wasmHOpenXPS_trapAborts`, `wasmHOpenXP_trapAborts`): a host trap, or (in the
  session module) an internal call answered by a trap, is the last call of the function, which
  then ends in a trap: `.ret (.inr ()) s'` keeping the store in the session module (a body
  ending in a trap flow, a pending tail call answered by a trap, a host function whose result is
  a trap), `.trap` in the canonical one.
* **Closures** (`wasmEvFunXPS_trapAborts`, `wasmEvFunXP_trapAborts`): in every finished behaviour
  of `wasmEvFunXPS` (resp. `wasmEvFunXP`), a host trap is the last host call, and the behaviour
  ends `.ret (.inr ()) s` (resp. `.trap`).
* **Divergence, pending calls, streams** (`wasmEvFunDXP_div_noTrap`, `wasmEvPendXP_noTrap`,
  `wasmEvInfNXP_noTrap`): no divergent behaviour, no prefix of a pending call and no productive
  stream contains a host trap; their internal calls all return.
* **The session triple** (`sessionTripleXP_trapAbortsRound`): `TrapAbortsRound IsHostTrap
  sessionTripleXP`; hence (`threadS_sessionTripleXP_trapAbortsBelow`) in every play of
  `threadS sessionTripleXP s₀`, a host trap is followed, if at all, by the trap answer `.inr ()`
  of the current invocation, and no further host call is made in that round
  (`threadS_sessionTripleXP_trapEndsBelow`).

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostTrapS`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Games.Abstract.SessionTrap Silmaril.Games.Abstract.StratSession
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **A trap answer ends the session run in a trap flow.** -/
theorem evalLXPS_trapLast {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    TrapLast (TrapCall (sh := wasmHShapeS H) IsHostTrap (trapEndS H)) (r.2.2 = .flow .trap) l :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.evalLXPS_trapLast h

/-! ## Open modules and closures -/

/-- **In the session open module, a trapped call ends the function with a trap.** -/
theorem wasmHOpenXPS_trapAborts :
    OpenTrapAborts IsHostTrap (trapEndS H) (wasmHOpenXPS (H := H)) :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmHOpenXPS_trapAborts

/-- **In the canonical open module, a host trap ends the function with `.trap`.** -/
theorem wasmHOpenXP_trapAborts :
    OpenTrapAborts IsHostTrap (trapEndH H) (wasmHOpenXP (H := H)) :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmHOpenXP_trapAborts

/-- **A host trap is the last host call of a session behaviour, which ends in a trap.** -/
theorem wasmEvFunXPS_trapAborts {s : Store H} {p : Nat × List Val}
    {c d : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} {n : Store H × Result}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} (hT : IsHostTrap m n)
    (h : (c ++ ⟨m, n⟩ :: d, e) ∈ wasmEvFunXPS s p) : d = [] ∧ TrapEnd e :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmEvFunXPS_trapAborts p.1 s p.2 _ h c ⟨m, n⟩ d rfl hT

/-- **A host trap is the last host call of a canonical behaviour, which ends `.trap`.** -/
theorem wasmEvFunXP_trapAborts {s : Store H} {p : Nat × List Val}
    {c d : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} {n : Store H × Result}
    {e : End (Store H) (List Val ⊕ Nat)} (hT : IsHostTrap m n)
    (h : (c ++ ⟨m, n⟩ :: d, e) ∈ wasmEvFunXP s p) : d = [] ∧ e = .trap :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmEvFunXP_trapAborts p.1 s p.2 _ h c ⟨m, n⟩ d rfl hT

/-! ## Divergence, pending calls, streams -/

/-- **A divergent canonical behaviour has no host trap.** -/
theorem wasmEvFunDXP_div_noTrap {s : Store H} {p : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunDXP s p) :
    ∀ e ∈ cs, ¬ IsHostTrap e.1 e.2 :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmEvFunDXP_div_noTrap h

/-- **No pending host call follows a host trap.** -/
theorem wasmEvPendXP_noTrap {s : Store H} {p : Nat × List Val}
    {q : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (h : (q, m) ∈ wasmEvPendXP s p) :
    ∀ e ∈ q, ¬ IsHostTrap e.1 e.2 :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.pendLXP_noTrap h

/-- **No productive stream has a host trap.** -/
theorem wasmEvInfNXP_noTrap {s : Store H} {p : Nat × List Val} {ω : Nat → Call (wasmHostSig H)}
    (h : ω ∈ wasmEvInfNXP s p) (k : Nat) : ¬ IsHostTrap (ω k).1 (ω k).2 :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.wasmEvInfNXP_noTrap h k

/-! ## The session triple -/

/-- **The native session triple aborts every round at a host trap.** -/
theorem sessionTripleXP_trapAbortsRound :
    TrapAbortsRound IsHostTrap (sessionTripleXP (H := H)) :=
  Silmaril.Proofs.Wasm.Abstract.HostTrapS.sessionTripleXP_trapAbortsRound

/-- **After a host trap, the native Wasm session answers the trap `.inr ()`**, if it moves at
all. -/
theorem threadS_sessionTripleXP_trapAbortsBelow (s₀ : Store H) :
    TrapAbortsBelow IsHostTrap (threadS (sessionTripleXP (H := H)) s₀) :=
  threadS_trapAbortsBelow sessionTripleXP_trapAbortsRound s₀

/-- **After a host trap, the native Wasm session makes no further host call in the round.** -/
theorem threadS_sessionTripleXP_trapEndsBelow (s₀ : Store H) :
    TrapEndsBelow IsHostTrap (threadS (sessionTripleXP (H := H)) s₀) :=
  (threadS_sessionTripleXP_trapAbortsBelow s₀).trapEndsBelow

end Silmaril.Wasm.Abstract
