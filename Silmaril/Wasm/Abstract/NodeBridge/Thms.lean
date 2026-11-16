module

public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
import Silmaril.Proofs.Wasm.Abstract.NodeBridge.Basic

/-!
# Core 3.0 instances seen through the Core host interface: theorems

**The universal store-preserving host.** `instHost I` is store-preserving
(`storePreserving_instHost`) and never diverges.

**Activations are Core runs** (every profile `P`, every store, no typing hypothesis). An
activation of the instance on the export question `a`, with import log `c`, is a labelled Core
run of the invocation `qOf I a` against `instHost I` whose host events `cs` view `c`
(`List.Forall₂ (CallView I) c cs`):

* `ret_iff`: a returning activation answering `v` and ending idle at `s'` is a run in the empty
  frame to a Core result `r` with `Answer.ofResult? r = some v`, at the store `s'` (values,
  uncaught exception, or a Wasm trap with its store);
* `div_iff`: host-free divergence after the log is host-free Core divergence after the run;
* `pend_iff`: a pending import call `e` is a reached Core callout `(hh, s', us)` reading as `e`;
* `inf_iff`: a productive run is a productive Core run (`CoreInf`) viewing its stream.

**The triple** (`instTripleS_eq_viewTriple`):

`instTripleS I P = viewTriple I (coreTripleSO P (instHost I))`.

The open instance triple of `InstSession` is the view of the open store-retaining Core triple
with exceptions at the universal store-preserving typed host. The finished behaviours and
productive streams on the right are those of the H2 owner's `coreTripleSXP P (instHost I)` on all
questions (`coreTripleSO_fst`, `coreTripleSO_inf`). The pending calls are all the reached
callouts, which contain `coreTripleSXP`'s pending calls (`coreTripleSXP_pend_sub`). The pending
calls of `coreTripleSXP` itself are blocked or host-divergent callouts. At `instHost I` none of
them has a view (`not_mem_view_pend_coreTripleSXP`): an answered callout is never a pending call
of `coreTripleSXP`. So the equality needs `coreTripleSO`, not `coreTripleSXP`.

**Sessions and the component semantics.** Hence the instance session is the session of the viewed
Core triple (`instSession_eq_view`), and the node sessions of the divergence-observing Core
3.0 component semantics are the viewed Core sessions:

* `core3SemD_eq_view : core3SemD P = threadSemSD fun m =>
    threadS (viewTriple m.inst (coreTripleSO P (instHost m.inst))) m.inst.store`;
* `core3Sem_eq_view`, and `denUD_core3SemD_eq_view`/`denD_core3SemD_eq_view` for `Comp.denUD`
  and `Comp.denD`.

## What is not claimed

* **A fixed store-dependent host is not a value-level environment.** The theorem closes the
  Core triple against the *universal* store-preserving host, which is open again. A fixed
  host `R` that is store-preserving but reads the store has in general no counterpart
  `hostD R'` on `I.E`. For example, take an export `g x` that writes `x` to memory and returns
  the result of `import0 ()`, and a host answering `import0` with the memory cell. Closed against
  it, `g 1` returns `1` and `g 2` returns `2`. Any host relation on `I.E` answers the same
  question `import0 ()` the same way at both calls, so the composite with `instSession` cannot
  return both.
* `TrapAbortsRound`/`TrapPropagating` for `core3SemD` nodes: proved in `Wasm.Abstract.NodeTrap`
  (`instTripleS_trapAbortsRound`, `trapPropagating_core3SemD`), directly on instance paths.
* The node strategies on `sigS` (`toU`/`ofU`). `core3SemD_eq_view` identifies the session
  object of each node, which `semOfSD` then wraps in the `core3Sem` coercions (`importH`,
  `exportH`). These theorems do not relate those coercions to `toU`/`ofU`.

Proofs in `Silmaril.Proofs.Wasm.Abstract.NodeBridge.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.NodeBridge

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component (Comp)
open Silmaril.Wasm.Component.Reference (NumInstance core3Sem)
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

/-! ## The universal host -/

/-- The universal host of `I` preserves the store. -/
theorem storePreserving_instHost : StorePreserving (instHost I) := by
  rintro _ _ _ _ _ ⟨_, -, _, h⟩
  exact (Silmaril.Wasm.Execution.Host.Outcome.returned.inj h).1

/-- The universal host of `I` never diverges. -/
theorem not_instHost_diverged {hh : Nat} {s : Store Nat} {us : List Val} :
    ¬ instHost I hh s us .diverged := by
  rintro ⟨_, -, _, h⟩; cases h

/-! ## Activations are Core runs -/

/-- **A returning activation is a labelled Core run, in the empty frame, to a result it reads.** -/
theorem ret_iff {s s' : Store Nat} {a : I.F.Op} {v : I.F.Ar a} {c : List (Call I.E)} :
    I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a v)])) (.idle s') ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ r, Answer.ofResult? (I.exports.get a.1) r = some v ∧
        EvRun P (instHost I) (invoke s (qOf I a).1 (qOf I a).2) cs ⟨s', {}, r.toAdmin⟩ :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.ret_iff

/-- **A divergent activation is a labelled Core run followed by host-free divergence.** -/
theorem div_iff {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (∃ s' t, I.Path P (.idle s) (.inr (.ask a) :: callMoves c) (.running a s' t) ∧
        InstStrat.Diverges P (s', t)) ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ c', EvRun P (instHost I)
        (invoke s (qOf I a).1 (qOf I a).2) cs c' ∧ Diverges P (fun _ _ _ _ => False) c' :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.div_iff

/-- **A pending import call is a reached Core callout reading as it.** -/
theorem pend_iff {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} {e : I.E.Op} :
    (∃ q, I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask e)])) q) ↔
      ∃ cs, List.Forall₂ (CallView I) c cs ∧ ∃ m : (wasmHostSig Nat).Op,
        I.importOp? m.1 m.2.2 = some e ∧ CoreCallout P (instHost I) s (qOf I a) (cs, m) :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.pend_iff

/-- **A productive run of the instance is a productive Core run viewing its stream.** -/
theorem inf_iff {s : Store Nat} {a : I.F.Op} {ω : ℕ → Call I.E} :
    ω ∈ InstStrat.instInf I P s a ↔ ∃ ω', CoreInf P (instHost I)
      (invoke s (qOf I a).1 (qOf I a).2) ω' ∧ ∀ k, CallView I (ω k) (ω' k) :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.inf_iff

/-! ## The open Core triple -/

section Open

variable {H : Type} {host : HostSemantics H}

theorem coreTripleSO_fst : (coreTripleSO P host).1 = (coreTripleSXP P host fun _ _ => True).1 :=
  rfl

theorem coreTripleSO_inf :
    (coreTripleSO P host).2.2 = (coreTripleSXP P host fun _ _ => True).2.2 := rfl

/-- The pending calls of `coreTripleSXP` (blocked or host-divergent callouts) are reached
callouts. -/
theorem coreTripleSXP_pend_sub (s : Store H) (q : Nat × List Val) :
    (coreTripleSXP P host fun _ _ => True).2.1 s q ⊆ (coreTripleSO P host).2.1 s q := by
  rintro ⟨cs, hh, s', us⟩ ⟨-, ⟨c, E, a', h₁, h₂, h₃, -⟩ | ⟨c, E, a', h₁, h₂, h₃, -⟩⟩ <;>
    exact ⟨c, E, a', h₁, h₂, h₃⟩

end Open

/-- At the universal host, **no pending call of `coreTripleSXP` has a view**: a callout reading as
an import question is answered (at least by a trap), so it is neither blocked nor
host-divergent. -/
theorem not_mem_view_pend_coreTripleSXP (s : Store Nat) (a : I.F.Op)
    (x : List (Call I.E) × I.E.Op) :
    x ∉ (viewTriple I (coreTripleSXP P (instHost I) fun _ _ => True)).2.1 s a :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.not_mem_view_pend_coreTripleSXP s a x

/-! ## The triple, the session and the component semantics -/

/-- **The open instance triple is the view of the open Core triple at the universal
store-preserving host.** -/
theorem instTripleS_eq_viewTriple :
    instTripleS I P = viewTriple I (coreTripleSO P (instHost I)) :=
  Silmaril.Proofs.Wasm.Abstract.NodeBridge.instTripleS_eq_viewTriple

/-- **The instance session is the session of the viewed Core triple.** -/
theorem instSession_eq_view (s : Store Nat) :
    instSession I P s = threadS (viewTriple I (coreTripleSO P (instHost I))) s :=
  congrArg (threadS · s) instTripleS_eq_viewTriple

/-- **The node sessions of `core3SemD P` are the viewed Core sessions.** -/
theorem core3SemD_eq_view (P : Profile) :
    core3SemD P = threadSemSD fun m =>
      threadS (viewTriple m.inst (coreTripleSO P (instHost m.inst))) m.inst.store :=
  congrArg threadSemSD (funext fun m => instSession_eq_view (I := m.inst) m.inst.store)

/-- The finite-play Core 3.0 component semantics is built from the viewed Core sessions. -/
theorem core3Sem_eq_view (P : Profile) :
    core3Sem P = threadSemS fun m =>
      threadS (viewTriple m.inst (coreTripleSO P (instHost m.inst))) m.inst.store := by
  rw [core3Sem_eq_threadSemS]
  exact congrArg threadSemS (funext fun m => congrArg (threadS · m.inst.store)
    (instTripleS_eq_viewTriple (I := m.inst) (P := P)))

/-- **Component denotations over Core 3.0 instances, with divergence, are those of the viewed Core
sessions.** -/
theorem denUD_core3SemD_eq_view (P : Profile) (c : Comp NumInstance) :
    c.denUD (core3SemD P) = c.denUD (threadSemSD fun m =>
      threadS (viewTriple m.inst (coreTripleSO P (instHost m.inst))) m.inst.store) := by
  rw [core3SemD_eq_view]

/-- The same at the interface signatures. -/
theorem denD_core3SemD_eq_view (P : Profile) (c : Comp NumInstance) :
    c.denD (core3SemD P) = c.denD (threadSemSD fun m =>
      threadS (viewTriple m.inst (coreTripleSO P (instHost m.inst))) m.inst.store) := by
  rw [core3SemD_eq_view]

end Silmaril.Wasm.Abstract.NodeBridge
