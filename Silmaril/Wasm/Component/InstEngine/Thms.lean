module

public import Silmaril.Wasm.Component.InstEngine.Defs
import Silmaril.Proofs.Wasm.Component.InstEngine.Basic

/-!
# The engine semantics with an instantiation phase: theorems

All proved, for an arbitrary engine `E`; proofs in
`Silmaril.Proofs.Wasm.Component.InstEngine.Basic`. `[inst] ++ cs ++ [a]` stands for the play
`instPlay cs a`: `askInst`, then `ask q, ans q r` for each import call `⟨q, r⟩` of
`cs`, then `ansInst a`.

**Instantiation.** For an instance `J` (`I = some J`) whose start function is at `a`:

* `engineStrategyI_inst_ready`: if the start phase (`StartRunI`) makes the import calls `cs` and
  returns values, then `[inst] ++ cs ++ [ready]` is a play;
* `engineStrategyI_inst_fail`: if it makes the calls `cs` and traps, then
  `[inst] ++ cs ++ [fail ()]` is a play;
* `engineStrategyI_noStart`: without a start function `[inst, ready]` is a play.

**The export phase is `engineStrategy`.**

* `engineStrategyI_after_start`: after a start phase returning at store `s'`, every play of
  `engineStrategy E ⟨s', J.addrs⟩` (lifted) follows the instantiation play;
* `engineSemI_after_ready`: for a module whose instance has no start function, every play of the
  start-free `engineSem` follows `[inst, ready]` in `engineSemI`.

Only these inclusions are proved; that the export phase has no other plays is not.
-/

public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Game (liftMove)

variable {E : Engine} {I : Option (IInstance E)} {imps exps : CoreIface}

/-- **A start phase returning values: instantiation succeeds**, its import calls as moves. -/
theorem engineStrategyI_inst_ready {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys)) :
    instPlay (F := sigN exps.length) cs .ready ∈ engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_inst_ready hI ha hr hf

/-- **A start phase trapping: instantiation fails**, its import calls as moves. -/
theorem engineStrategyI_inst_fail {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c')
    (hf : E.status c'.1 c'.2 = .returned .trap) :
    instPlay (F := sigN exps.length) cs (.fail ()) ∈ engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_inst_fail hI ha hr hf

/-- **Without a start function the instance is ready at once.** -/
theorem engineStrategyI_noStart {J : IInstance E} (hI : I = some J) (ha : J.start = none) :
    [askInst, ansInst .ready] ∈ engineStrategyI E I imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_noStart_ready hI ha

/-- **After a successful start phase, the exports are served as `engineStrategy` serves them
from the store the start function left.** -/
theorem engineStrategyI_after_start {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys))
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (hp : p ∈ engineStrategy E ⟨c'.1, J.addrs⟩ imps exps) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈
      engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_after_start hI ha hr hf hp

/-- **On start-free modules `engineSemI` extends `engineSem`**: after `[inst, ready]`, every play
of the start-free engine semantics is a play. -/
theorem engineSemI_after_ready {M : Type} [CoreModule M] {emb : M → E.Module} {m : M}
    {J : IInstance E}
    (h : instOfI E (emb m) (CoreModule.imports m) (CoreModule.exports m) = some J)
    (hs : J.start = none) {p : List (Move (sigN (CoreModule.imports m).length)
      (sigN (CoreModule.exports m).length))} (hp : p ∈ (engineSem E M emb).sem m) :
    askInst :: ansInst .ready :: p.map liftMove ∈ (engineSemI E M emb).sem m :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engineSem_le_after h hs hp

end Silmaril.Wasm.Component.Param
