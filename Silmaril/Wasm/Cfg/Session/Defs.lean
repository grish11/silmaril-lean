module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Wasm.Cfg.FunctionCfg.Defs
public import Silmaril.Wasm.Cfg.Machine.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Defs

@[expose] public section

/-!
# The store-retaining session of a host-free instance, run by the block-CFG machine

A scalar Core 3.0 instance `I : ScalarInstance` is read as a store-retaining session
(`InstSession.instSession I P s = StratSession.threadS (instTripleS I P) s`). This module defines
the same kind of object from the **block-CFG machine** (`Silmaril.Wasm.Cfg.Machine`) instead of
from Core 3.0 runs: one export activation is a run of the machine on the exported function's body,
in its call frame, from the CFG entry.

## One activation on the CFG machine

For the export question `a` (export `a.1` with the typed arguments `a.2.1`) at the store `s`,
the exported function is `fi = s.funcs[I.addr a.1]`, with Wasm code `fn` and type `ps → rs`.

* `CfgRet I o s a r s'`: the machine `MStepC (profile o) noHostX (CX closedCallX) fn.body` runs
  from `initial fn.body s (Frame.forCall fi.module a.2.1 fn.locals)` to a sink state `st` that
  reads as the result `r` (`sinkResult rs.length st = some r`) and whose store is `s'`.
* `CfgDiv I o s a`: the machine diverges on the body in that frame (`MDivT … (calleeDivX o)`):
  an infinite machine run, or a finite run to a call or tail call of a callee that diverges.
* `sinkResult n st`: at `exit`, the top `n` values of the machine stack, bottom first (the stack
  is the whole frame stack: the machine keeps the label frames' outer values under the block's
  at every exit, see `MStepC.ret`, `brOut`, …); at `trap`, a trap (keeping the store); at
  `raise` with the stack `[ref (exn t)]`, the uncaught exception `t`. Other states read as
  nothing.

`cfgFinS I o s a` is the activation's finished behaviours: `([], .ret (sAns a v) s')` for an
answer `v` the result `r` of a `CfgRet` reads as (`Answer.ofResult?`, so values are typed at the
export's result types), and `([], .div)` for `CfgDiv`. The activation makes no host calls, so its
log is empty. A trap is `.ret (.inr ()) s'`, keeping the trap store `s'`, as in `instFinS`.

`cfgTripleS I o := (cfgFinS I o, ∅, ∅)`: **no pending import calls and no productive streams of
import calls inside an activation**, since the machine never calls a host. This is not a claim
that the session has no infinite plays: `cfgSession I o s := StratSession.threadS (cfgTripleS I o)
s` has every coherent infinite sequence of export rounds (`StratThread.InfRounds`), trap-resume
rounds included, as its infinite plays (`Session.mem_inf_cfgSession`).

`cfgSessions o m`: the numeric instance `m` by its CFG session at its instantiation store when it
is in the fragment there, and by its instance session otherwise. **The fallback is compatibility
only, not CFG coverage**: outside `HFOk` the instance is still interpreted by Core 3.0, and nothing
here gives a CFG semantics to modules with imports, hosts, exceptions or unchecked code.

## The oracle

The machine answers every call (direct, indirect, by reference, tail) with the typed closed
extended oracle `CX closedCallX`, and names the diverging callees by `calleeDivX o`: **this is an
oracle-backed interprocedural CFG semantics**, not a self-contained recursive CFG machine. The
oracle `closedCallX` is the least fixpoint of running each callee's body in the native extended
interpreter (`Abstract.CallX.EvalOX`), and `calleeDivX o` is Core 3.0 divergence of the callee's
invocation. The equality with the instance session (`Session.cfgSession_eq_instSession`) uses
the proven Core-soundness of this oracle on the fragment; replacing the oracle by a recursive
run of the CFG machine on each callee is separate work.

## The fragment (`HFOk I s`)

`HFOk I s` states the explicit host-free typed fragment: no imports (`I.imports = []`), the
instance is well formed at `s` (`I.WellFormed s`: `StoreOk s`, every export address has its
declared type), every function of `s` is a Wasm function with a function type (`WasmFuncsT s`,
so no host functions at all), and every function passes the tail-aware arity check
`Interp.StoreChkE Interp.tExt s.funcs`. The check `tExt` covers every call form; it rejects
`throw` and `try_table`, so the fragment has no exceptions. **No host is a separate condition
from no exceptions**: an instance without imports could still throw, and the fragment excludes
exceptions through `tExt`, not through the absence of hosts.

Theorems in `Silmaril.Wasm.Cfg.Session.Thms`.
-/

namespace Silmaril.Wasm.Cfg.Session

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.InstSession (Res sAns)
open Silmaril.Wasm.Abstract.XRecursion (closedCallX)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **The result a sink state reads as**: at `exit` the top `n` values of the stack (bottom
first), at `trap` a trap, at `raise` the exception on the stack. -/
def sinkResult {H : Type} (n : Nat) (st : MState H) : Option Result :=
  match st.node, st.stk with
  | .exit, stk => some (.values (stk.reverse.take n).reverse)
  | .trap, _ => some .trap
  | .raise, [.ref (.exn t)] => some (.throw t)
  | _, _ => none

variable (I : ScalarInstance) (o : GrowOracle)

/-- **A returning activation on the CFG machine**: the machine runs the body of the function of
export `a.1`, in its call frame on the arguments `a.2.1`, from the CFG entry to a sink state
reading as `r` with the store `s'`. -/
def CfgRet (s : Store Nat) (a : I.F.Op) (r : Result) (s' : Store Nat) : Prop :=
  ∃ (fi : FuncInst Nat) (fn : Func) (ps rs : List Validation.CValType) (st : MState Nat),
    s.funcs[I.addr a.1]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    Relation.ReflTransGen (MStepC (profile o) noHostX (CX (closedCallX : Abstract.CallRel Nat))
      fn.body) (initial fn.body s (Frame.forCall fi.module a.2.1 fn.locals)) st ∧
    sinkResult rs.length st = some r ∧ st.store = s'

/-- **A divergent activation on the CFG machine**: frame divergence (`MDivT`) of the machine on
the body of the function of export `a.1`, in its call frame, from the CFG entry. -/
def CfgDiv (s : Store Nat) (a : I.F.Op) : Prop :=
  ∃ (fi : FuncInst Nat) (fn : Func) (ps rs : List Validation.CValType),
    s.funcs[I.addr a.1]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    MDivT (profile o) noHostX (CX (closedCallX : Abstract.CallRel Nat)) (Function.calleeDivX o)
      fn.body (initial fn.body s (Frame.forCall fi.module a.2.1 fn.locals))

/-- **The finished behaviours of one activation on the CFG machine**: the answer read from the
sink state with its store (a trap keeps its store), or divergence; the log is empty. -/
def cfgFinS : AFun I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) := fun s a =>
  {x | x.1 = [] ∧ ((∃ (v : I.F.Ar a) (s' : Store Nat) (r : Result), x.2 = .ret (sAns a v) s' ∧
      Answer.ofResult? (I.exports.get a.1) r = some v ∧ CfgRet I o s a r s') ∨
    (x.2 = .div ∧ CfgDiv I o s a))}

/-- **The store-retaining CFG triple**: the machine's activations, no pending import calls and
no productive import streams inside an activation. -/
def cfgTripleS : ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  (cfgFinS I o, fun _ _ => ∅, fun _ _ => ∅)

/-- **The session of the instance run by the CFG machine** from the store `s`. -/
def cfgSession (s : Store Nat) : DStrategy I.E (Abstract.InstSession.ssig I.exports) :=
  StratSession.threadS (cfgTripleS I o) s

/-- **The host-free typed fragment** at the store `s` (see the module docstring). -/
structure HFOk (s : Store Nat) : Prop where
  noImports : I.imports = []
  wf : I.WellFormed s
  wasm : WasmFuncsT s
  chk : StoreChkE tExt s.funcs

open Classical in
/-- **Each numeric instance by its CFG session where the fragment applies**: the CFG session at
the instantiation store when `HFOk` holds there, the instance session (Core 3.0) otherwise. The
fallback keeps the component semantics unchanged; it is not CFG coverage outside `HFOk`. -/
noncomputable def cfgSessions (o : GrowOracle) (m : Component.Reference.NumInstance) :
    DStrategy m.inst.E (Abstract.InstSession.ssig m.inst.exports) :=
  if HFOk m.inst m.inst.store then cfgSession m.inst o m.inst.store
  else Abstract.InstSession.instSession m.inst (profile o) m.inst.store

end Silmaril.Wasm.Cfg.Session
