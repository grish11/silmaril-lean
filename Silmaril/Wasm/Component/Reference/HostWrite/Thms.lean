module

public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
import Silmaril.Proofs.Wasm.Component.Reference.HostWrite.Runs

/-!
# Host-state writes along machine runs: theorems

**Scope.** The reference machine `Machine.Step` over every core engine, with the reference
dispatcher `Canon.dispatch lim q hr host`; and in particular the logging answering host
`answerImplS (HLinked2.logG g)` of the `HLinked2` session observations (`HLinked2.sessObs`,
`HLinked2.refDivs`) on `core3P P`, at every profile `P`.

**Hypotheses.** For the general theorems, a host whose programs are host-safe (`HostImplSafe`);
the logging host is one (`hostImplSafe_answerLog`). No hypothesis on the component.

## Proved

* **The program logic** (`HostSafe.of_invW`): a program certified by `P.InvW I (fun _ => False)`
  never writes the host state and is host-safe for every `Ext`. `P.InvW` is the program logic of
  the reference programs (`Canon.Effects`) with a host-write constraint; every program-logic
  lemma of the reference programs holds at every host-write constraint.
* **The reference dispatcher** (`hostSafe_dispatch`): every program of `Canon.dispatch` is
  host-safe for a host-safe host. Canon lift and lower, the loops and thread bodies, every canon
  built-in, the caller records, nested invokes and cancellations and nested instantiation never
  write the host state.
* **The logging host** (`hostImplSafe_answerLog`): `answerImplS (HLinked2.logG g)` is host-safe for
  `logExt`. Its host function reads the host state `s` and, as its very next operation, writes
  `(s₁, s.2 ++ [e])` (or traps): the write is of the *current* state, never a stale read, because
  the machine runs the head program and no step separates a read from the write right after it.
* **Every machine step** (`step_cfgSafe`, `step_host`): from a host-safe configuration a step
  reaches a host-safe configuration, and the host state is unchanged or related by `Ext`
  (`hostSet` is the only rule that changes it).
* **Runs, instantiation, calls and sessions** (`steps_cfgSafe`, `instantiates_cfgSafe`,
  `calls_cfgSafe`, `sessRun_cfgSafe`, `cfgSafe_init`): host-safety holds from the initial
  configuration through root instantiation, top-level calls and resumable sessions (`resumeCfg`
  after a trapped call keeps the programs of the configuration before the call, whose control
  chain is empty).
* **The log of a logging session only grows** (`HLinked2.logSession_cfgSafe`,
  `HLinked2.logSteps_mono`): after instantiating a component under the logging host from the
  host functions of `ims` and running a resumable session, every run without host-frame
  programs leaves the host state unchanged or strictly extends its log.

## Not claimed

* Hosts whose programs write the host state otherwise (for example a host that restores an
  older state) are not host-safe for `logExt`; the theorems are about the logging host.
* The table frame argument (`Silmaril.Proofs.Wasm.Resource.MachineTab`) follows the same
  structure for handle tables; the two are not yet derived from one parametric dispatcher lemma.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HostWrite.{Prog, Dispatch, Step, Runs}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

section General

variable {E : CoreEngine} {σ : Type} {Ext : σ → σ → Prop}

/-- **Programs that never write the host state are host-safe** (proved). -/
theorem HostWrite.hostSafe_of_invW {α : Type} {I : CStore E → Prop} {p : P E σ α}
    (h : P.InvW I (fun _ : σ => False) p) (c : Option σ) : HostSafe Ext c p :=
  Canon.HostSafe.of_invW h c

/-- **Every program of the reference dispatcher is host-safe, for a host-safe host** (proved). -/
theorem HostWrite.hostSafe_dispatch [∀ a b, Decidable (E.ExternSub a b)] {host : HostImpl E σ}
    (hh : HostImplSafe Ext host) (lim : Silmaril.Wasm.Component.Limits) (q : Quirks)
    (hr : HostReady σ) : DispatchSafe Ext (dispatch lim q hr host) :=
  Silmaril.Proofs.Wasm.Component.Reference.HostWrite.hostSafe_dispatch hh lim q hr

/-- **The logging answering host is host-safe for `logExt`** (proved). -/
theorem HostWrite.hostImplSafe_answerLog {σ₀ : Type}
    (g : σ₀ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ₀)) :
    HostImplSafe (E := E) logExt (answerImplS (HLinked2.logG g)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HostWrite.hostImplSafe_answerLog g

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

/-- **A step keeps host-safety** (proved). -/
theorem HostWrite.step_cfgSafe (hd : DispatchSafe Ext dispatch) {m m' : Config E σ}
    {l : Label E σ} (h : Step prof hr dispatch m l m') (hm : CfgSafe Ext m)
    (hl : ∀ p, l = .host (.run p) → HostSafe Ext none p) : CfgSafe Ext m' :=
  Silmaril.Proofs.Wasm.Component.Reference.HostWrite.step_cfgSafe hd h hm hl

/-- **Along a step from a host-safe configuration the host state is unchanged or the step is a
write allowed by `Ext`** (proved). -/
theorem HostWrite.step_host {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') (hm : CfgSafe Ext m) :
    m'.host = m.host ∨ Ext m.host m'.host :=
  Silmaril.Proofs.Wasm.Component.Reference.HostWrite.step_host h hm

/-- **Runs keep host-safety** (proved). -/
theorem HostWrite.steps_cfgSafe (hd : DispatchSafe Ext dispatch) {m m' : Config E σ}
    {tr : List (Label E σ)} (h : Steps prof hr dispatch m tr m') (hm : CfgSafe Ext m)
    (hl : RunSafe Ext tr) : CfgSafe Ext m' :=
  (Silmaril.Proofs.Wasm.Component.Reference.HostWrite.steps_cfgSafe hd h hm hl).1

/-- The initial configurations are host-safe (proved). -/
theorem HostWrite.cfgSafe_init (s : CStore E) (σ0 : σ) : CfgSafe Ext (Config.init s σ0) :=
  Silmaril.Proofs.Wasm.Component.Reference.HostWrite.cfgSafe_init s σ0

end General

namespace HLinked2

variable {P : Profile} {prof : ProfileKind} {σ₀ : Type}
  {g : σ₀ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
    Option (List Silmaril.Wasm.Component.Value.Val × σ₀)}

/-- **The configurations of a logging session are host-safe** (proved): after instantiating a
component under the logging host from the host functions of `ims` and running a resumable
session, every program of the configuration reached is host-safe for `logExt`. -/
theorem logSession_cfgSafe {ims : Iface} {s₀ : σ₀ × List HostEvent}
    {c : CompAst (core3P P).Module} {m₀ m₁ : Machine.Config (core3P P) (σ₀ × List HostEvent)}
    {inst : InstId} {es : List (String × FuncId)} {k : Nat}
    {calls : List (FuncId × List Silmaril.Wasm.Component.Value.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof (answerHostS P (logG g))
      (LinkedSession.hostConfig ims s₀) c (importArgs ims))
    (hs : LinkedSession.SessRun prof (answerHostS P (logG g)) m₀ k calls outs m₁) :
    CfgSafe logExt m₁ := by
  have hd : DispatchSafe logExt (answerHostS P (logG g)).dispatch :=
    HostWrite.hostSafe_dispatch (HostWrite.hostImplSafe_answerLog g) _ _ _
  exact Silmaril.Proofs.Wasm.Component.Reference.HostWrite.sessRun_cfgSafe hd hs
    (Silmaril.Proofs.Wasm.Component.Reference.HostWrite.instantiates_cfgSafe hd hi
      (HostWrite.cfgSafe_init _ _)).1

/-- **The log of a logging session only grows** (proved): from a host-safe configuration of the
logging host, a run without host-frame programs leaves the host state unchanged or strictly
extends its log. -/
theorem logSteps_mono {m m' : Machine.Config (core3P P) (σ₀ × List HostEvent)}
    {tr : List (Label (core3P P) (σ₀ × List HostEvent))} (hm : CfgSafe logExt m)
    (h : Steps prof (answerHostS P (logG g)).hr (answerHostS P (logG g)).dispatch m tr m')
    (hl : RunSafe logExt tr) : m'.host = m.host ∨ logExt m.host m'.host := by
  have hd : DispatchSafe logExt (answerHostS P (logG g)).dispatch :=
    HostWrite.hostSafe_dispatch (HostWrite.hostImplSafe_answerLog g) _ _ _
  exact Silmaril.Proofs.Wasm.Component.Reference.HostWrite.hostChain_logExt
    (Silmaril.Proofs.Wasm.Component.Reference.HostWrite.steps_cfgSafe hd h hm hl).2

end HLinked2

end Silmaril.Wasm.Component.Reference
