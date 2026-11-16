module

public import Silmaril.Wasm.Cfg.Session.Defs
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
import Silmaril.Proofs.Wasm.Cfg.Session

@[expose] public section

/-!
# The store-retaining session of a host-free instance, run by the block-CFG machine

**The fragment** (`HFOk I s`, stated explicitly): a scalar instance with **no imports**, well
formed at `s`, whose store holds only Wasm functions with function types (`WasmFuncsT`), all
passing the tail-aware arity check `Interp.StoreChkE Interp.tExt`, at a deterministic profile
`profile o`. `tExt` covers direct, indirect, by-reference and tail calls, and rejects `throw` and
`try_table`: the fragment has **no exceptions**, a condition separate from having no host. Full
Wasm stays unsupported here: instructions outside `tExt`, untyped stores, host functions and
imports are excluded by these hypotheses, not handled.

**The oracle.** The CFG machine answers calls with `CX closedCallX` (the closed extended native
oracle on typed entries) and names diverging callees by `calleeDivX o`. The CFG session is
therefore an **oracle-backed** interprocedural CFG semantics: the equality below uses the proven
Core-soundness and completeness of that oracle on the fragment (`Function.machine_core`,
`Function.core_machine`, `Function.invoke_diverges_iff_mdivT`), not a recursive CFG machine
running the callees.

* **`instFinS_eq`** (one activation): on the fragment, the finished behaviours of an export
  activation on the CFG machine (`cfgFinS`: the answer read from the sink state with its store,
  a trap keeping its store, or frame divergence `MDivT`) are those of the instance
  (`InstSession.instFinS`, defined by `ScalarInstance.Path` runs). The logs are empty on both
  sides (no imports), so this is not a definition by Core: the CFG side is a machine run, the
  instance side a Core 3.0 run, related by the function-level CFG theorems. Exit answers are read
  from the whole frame stack the machine keeps at `exit` (the top `rs.length` values);
  exceptions do not arise (`tExt`), which the proof derives (a closed outcome of a checked
  invocation is never a throw).
* **`hfOk_of_reach`**: the fragment persists at every store the session reaches: host-free runs
  keep the function list, and the instance stays well formed
  (`ScalarInstance.wellFormed_after_run`).
  This is not a claim about host-mutated stores.
* **`cfgSession_eq_instSession`**: on the fragment, **the CFG session is the instance session**
  (`StratSession.threadS_congr` at the reachable stores). Hence `spull_cfgSession`: its finite
  plays read back on the export interface are `I.strategy (profile o) s`.
* **`mem_inf_cfgSession`**: the infinite plays of the CFG session are exactly those of the
  coherent infinite sequences of export rounds of the CFG triple (`StratThread.InfRounds`), trap
  rounds that resume from the trap store included. An empty import interface rules out pending
  import calls and productive import streams inside a round, **not infinite session plays**:
  `infRounds_repeat` builds the infinite play repeating any round that returns to its own store,
  for instance a trap that leaves the store unchanged. `infRounds_iff`: these are the infinite
  rounds of the instance triple.
* **`core3SemD_eq_cfgSessions`**: the divergence-observing Core 3.0 component semantics
  `core3SemD (profile o)` interprets every numeric instance in the fragment at its instantiation
  store by its CFG session (and the others by their instance sessions, unchanged); hence
  `denUD_core3SemD_eq_cfgSessions` for the denotation of any component.

Not claimed here: hosts and imports (pending calls, logs, productive interaction), exceptions
(XP/EH), and a self-contained recursive CFG machine discharging the oracle; see
`docs/projects/wasm-cfg.md`.
-/

namespace Silmaril.Wasm.Cfg.Session

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Reach InfRounds)
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (Res ssig instFinS instTripleS instSession spull
  threadSemSD core3SemD)
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {I : ScalarInstance} {o : GrowOracle}

/-- **One activation on the CFG machine is one instance activation**, on the fragment. -/
theorem instFinS_eq {s : Store Nat} (h : HFOk I s) (a : I.F.Op) :
    instFinS I (profile o) s a = cfgFinS I o s a :=
  Proofs.Session.instFinS_eq h a

/-- **The fragment holds at every reachable store of the instance session.** -/
theorem hfOk_of_reach {s₀ s : Store Nat} (h : HFOk I s₀)
    (hr : Reach (instTripleS I (profile o)) s₀ s) : HFOk I s :=
  Proofs.Session.hfOk_of_reach h hr

/-- **The CFG session is the instance session**, on the fragment. -/
theorem cfgSession_eq_instSession {s : Store Nat} (h : HFOk I s) :
    cfgSession I o s = instSession I (profile o) s :=
  Proofs.Session.cfgSession_eq_instSession h

/-- The finite plays of the CFG session, read back on the export interface, are the instance's
strategy. -/
theorem spull_cfgSession {s : Store Nat} (h : HFOk I s) :
    spull (cfgSession I o s).toStrategy = I.strategy (profile o) s := by
  rw [cfgSession_eq_instSession h]
  exact Abstract.InstSession.spull_instSession s

/-- **Coherent infinite rounds of the CFG triple are those of the instance triple**, from a
store of the fragment. -/
theorem infRounds_iff {s₀ : Store Nat} (h : HFOk I s₀) {a : ℕ → I.F.Op}
    {r : ℕ → List (Call I.E) × (Res I.exports ⊕ PUnit)} {s : ℕ → Store Nat} :
    InfRounds (instTripleS I (profile o)) s₀ a r s ↔ InfRounds (cfgTripleS I o) s₀ a r s :=
  Proofs.Session.infRounds_iff h

/-- **The infinite plays of the CFG session** are the plays of the coherent infinite sequences
of export rounds, trap-resume rounds included. -/
theorem mem_inf_cfgSession {s₀ : Store Nat} (h : HFOk I s₀)
    {J : Set (List (Move I.E (ssig I.exports)))} :
    J ∈ (cfgSession I o s₀).inf ↔
      ∃ a r s, InfRounds (cfgTripleS I o) s₀ a r s ∧ J = StratSession.sroundsPlay a r :=
  Proofs.Session.mem_inf_cfgSession h

/-- **A round returning to its own store repeats forever**: its infinite repetition is an
infinite play of the CFG session (`mem_inf_cfgSession`), whether the round answers or traps. -/
theorem infRounds_repeat {s₀ : Store Nat} {a : I.F.Op} {b : Res I.exports ⊕ PUnit}
    (hb : ([], .ret b s₀) ∈ cfgFinS I o s₀ a) :
    InfRounds (cfgTripleS I o) s₀ (fun _ => a) (fun _ => ([], b)) (fun _ => s₀) :=
  ⟨rfl, fun _ => hb⟩

/-- **The divergence-observing Core 3.0 component semantics through CFG sessions**:
`core3SemD (profile o)` interprets every numeric instance that is in the fragment at its
instantiation store by its CFG session (`cfgSessions`), and the others by their instance
sessions. -/
theorem core3SemD_eq_cfgSessions :
    core3SemD (profile o) = threadSemSD (cfgSessions o) :=
  Proofs.Session.core3SemD_eq_cfgSessions

/-- **Component denotations through CFG sessions**: the divergence-observing denotation of any
component over Core 3.0 instances is the one interpreting its host-free instances by their CFG
sessions. -/
theorem denUD_core3SemD_eq_cfgSessions (c : Comp NumInstance) :
    c.denUD (core3SemD (profile o)) = c.denUD (threadSemSD (cfgSessions o)) := by
  rw [core3SemD_eq_cfgSessions]

end Silmaril.Wasm.Cfg.Session
