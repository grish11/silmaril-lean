module

public import Silmaril.Wasm.Cfg.MachineL.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Cfg.MachineLDiv.Defs

/-!
# The recursive CFG closure: definitions (H3)

`cfgHOpenXPS`: the open module whose Wasm functions run **on the logged block-CFG machine**
(`MachineL.MStepL`), as the session's open module `Abstract.wasmHOpenXPS` runs them by the native
relation `EvalLXPS`. It is defined from the machine, not as an alias:

* a Wasm function whose body runs from the CFG entry (`initial`, the call's frame
  `Frame.forCall`) to a sink (`exit`, `trap`, `raise`) with the log `l`. Its end is the sink's
  flow (`EndRel`) read at the function's result arity (`exitFlow`), keeping the store
  (`endOfFlowS`);
* a Wasm function whose body runs to a pending tail call (`TailL`, made at the function's frame):
  the log, then the tail call `SCall.mk a' args s₁ b s₂` with its answer, the end read from the
  answer (`tailAnsS`);
* a host function: one host call, as in `wasmHOpenXPS`.

`cfgEvFunXPS := Shape.close cfgHOpenXPS`: the closure resolves internal calls (and tail calls)
through functions run on the CFG machine.

`cfgHOpenXP`: the **canonical, trap-erasing** open module (`wasmHShape H`, logs of `OCall`s with
no trap answers), also run on the logged machine, as `Abstract.wasmHOpenXP` runs its bodies by
`EvalLXPh`. A machine log `lS` (of `SCall`s) is read as a canonical log `l` by `CanonRead`: it is
the session reading `l.map OCall.toS`, or it ends in a callee-trap answer
`SCall.mk g args s₁ (.inr ()) s₂`, read as the **cut call** `OCall.mk g args s₁ (.inl ws) s₂` for
every answer `ws` longer than the callee's result arity. The three cases:

* a Wasm body run from the CFG entry to a sink with the log `lS`, read as `l`; the end is the
  sink's flow read at the result arity, in the sink's store (`endOfFlow`, a trap erasing its
  store);
* a Wasm body run to a pending tail call, the logs `l₁ ++ l₂` the session reading of `l`; then the
  tail call `OCall.mk a' args s₁ b s₂` with its answer (`tailAns`);
* a host function: one host call, as in `wasmHOpenXP`.

`cfgEvFunXP := Shape.close cfgHOpenXP`.

**The CFG session triple** (`cfgSessionTriple`), the divergent and productive parts with bodies
run on the logged machine:

* `LDLcfg z u`: the body of the Wasm function called by `z` diverges on the machine after a log
  (`MachineL.MLogDivL`) that is the session reading (`OCall.toS`) of a canonical log `L`, and
  `u = L.map OCall.lift`;
* `InfLcfg`: the body runs productively on the machine (`MachineL.ProdL`), its stream the session
  reading of a canonical stream `ω`, lifted to calls of the module;
* `cfgEvFunDXP := Shape.closeDLog cfgHOpenXP LDLcfg`, `cfgEvInfNXP := Shape.closeInfL cfgHOpenXP
  InfLcfg`, and `cfgEvFunDXPS`: `cfgEvFunXPS` with the `div` behaviours of `cfgEvFunDXP`, as
  `Abstract.wasmEvFunDXPS`;
* `cfgSessionTriple := (cfgEvFunDXPS, cfgEvPendXPS, cfgEvInfNXP)`.

Theorems in `Silmaril.Wasm.Cfg.CfgSession.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmHShapeS SCall endOfFlowS tailAnsS exitFlow resFlow wasmHostSig
  wasmHShape OCall endOfFlow tailAns)

variable {H : Type}

/-- **The functions of a store, Wasm bodies run on the logged CFG machine**, host functions as
imports, traps keeping the store. -/
def cfgHOpenXPS : (wasmHShapeS H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (bfl fl : Flow) (l : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      st.node.IsSink ∧ EndRel st (st.store, st.frame, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l, endOfFlowS fl st.store)) ∨
    (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (s₁ s₂ : Store H) (f₂ : Frame) (a' n : Nat) (args : List Val)
      (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (l l' : List (SCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      TailL fn.body st l' (s₁, f₂, .tail a' args n) ∧
      x = ((l ++ l') ++ [SCall.mk a' args s₁ b s₂], tailAnsS rs.length n b s₂)) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlowS fl s'))}

/-- **The CFG session closure**: internal calls resolved through functions run on the CFG
machine. -/
def cfgEvFunXPS :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => Shape.close cfgHOpenXPS p.1 s p.2

/-- **Pending host calls of the CFG session**: as the session's `Abstract.PendLXPS`, with Wasm
bodies run on the CFG machine. A host function is pending at once. A Wasm function runs on the
machine to a block reaching an internal call (`ReachL`) or to a pending tail call (`TailL`); its
log so far is resolved by the CFG closure, and the call's own pending calls follow. -/
inductive CfgPendLXPS : Store H → Nat → List Val → List (Call (wasmHostSig H)) →
    (wasmHostSig H).Op → Prop where
  | self {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {hh : H}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) : CfgPendLXPS s a vs [] (hh, s, vs)
  | desc {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func} {st : MState H}
      {l₁ l₂ : List (SCall H)} {q q' : List (Call (wasmHostSig H))}
      {z : (Abstract.wasmOShape H).self.Op} {m : (wasmHostSig H).Op}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hrun : MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l₁ st)
      (hr : ReachL fn.body st l₂ z) (hq : Shape.SubstPre (Shape.close cfgHOpenXPS) (l₁ ++ l₂) q) :
      CfgPendLXPS z.2.2 z.1 z.2.1 q' m → CfgPendLXPS s a vs (q ++ q') m
  | tail {s s₁ : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func} {st : MState H}
      {f₂ : Frame} {a' n : Nat} {args : List Val} {l₁ l₂ : List (SCall H)}
      {q q' : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
      (hrun : MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l₁ st)
      (ht : TailL fn.body st l₂ (s₁, f₂, .tail a' args n))
      (hq : Shape.SubstPre (Shape.close cfgHOpenXPS) (l₁ ++ l₂) q) :
      CfgPendLXPS s₁ a' args q' m → CfgPendLXPS s a vs (q ++ q') m

/-- **The pending host calls of the CFG session.** -/
def cfgEvPendXPS : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => {x | CfgPendLXPS s p.1 p.2 x.1 x.2}

/-! ## The canonical, trap-erasing module on the machine -/

/-- **A machine log read as a canonical log.** The session log `lS` is the session reading
(`OCall.toS`) of `l`, or ends in a callee-trap answer to `g` leaving `s₂` and `l` is its cut
reading: the canonical log `u` before it, then the call answered by values `ws`, more than the
callee's result arity. -/
def CanonRead (lS : List (SCall H)) (l : List (OCall H)) : Prop :=
  lS = l.map OCall.toS ∨
  ∃ (u : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H) (ws : List Val)
    (fi : FuncInst H) (ps rs : List Validation.CValType),
    lS = u.map OCall.toS ++ [SCall.mk g args s₁ (.inr ()) s₂] ∧
    l = u ++ [OCall.mk g args s₁ (.inl ws) s₂] ∧ s₁.funcs[g]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧ rs.length < ws.length

/-- **The functions of a store, Wasm bodies run on the logged CFG machine**, host functions as
imports, the canonical trap-erasing module: machine logs read by `CanonRead`, a trap's store
erased. -/
def cfgHOpenXP : (wasmHShape H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (bfl fl : Flow) (lS : List (SCall H)) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) lS st ∧
      st.node.IsSink ∧ EndRel st (st.store, st.frame, .flow bfl) ∧ CanonRead lS l ∧
      exitFlow rs.length bfl = some fl ∧ x = (l.map OCall.lift, endOfFlow fl st.store)) ∨
    (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (st : MState H)
      (s₁ s₂ : Store H) (f₂ : Frame) (a' n : Nat) (args : List Val) (b : List Val ⊕ Nat)
      (l₁ l₂ : List (SCall H)) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l₁ st ∧
      TailL fn.body st l₂ (s₁, f₂, .tail a' args n) ∧ l₁ ++ l₂ = l.map OCall.toS ∧
      x = ((l ++ [OCall.mk a' args s₁ b s₂]).map OCall.lift, tailAns rs.length n b s₂)) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'))}

/-- **The canonical CFG closure**: internal calls resolved through functions run on the CFG
machine, traps erasing their store. -/
def cfgEvFunXP : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.close cfgHOpenXP p.1 s p.2

/-! ## The CFG session triple -/

open Silmaril.Wasm.Abstract (HCall) in
/-- **Logged divergence of a call on the machine**: the body of the Wasm function called by `z`,
run on the logged machine from the CFG entry at the call's frame, diverges after the session
reading of the canonical log `L` (`MLogDivL`); `u` is `L` as calls of the module. -/
def LDLcfg (z : (wasmHShape H).self.Op) (u : List (HCall H)) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (L : List (OCall H)), z.2.2.funcs[z.1]? = some fi ∧
    fi.code = .wasm fn ∧
    MLogDivL fn.body (initial fn.body z.2.2 (Frame.forCall fi.module z.2.1 fn.locals))
      (L.map OCall.toS) ∧
    u = L.map OCall.lift

/-- **Productive runs of a Wasm body on the machine**: the body runs productively on the logged
machine from the CFG entry at the call's frame (`ProdL`), its stream the session reading of the
canonical stream `ω`; the stream is `ω` as calls of the module. A host function has none. -/
def InfLcfg : Shape.OpenInf (wasmHShape H) := fun a s vs =>
  {ν | ∃ (fi : FuncInst H) (fn : Func) (ω : ℕ → OCall H), s.funcs[a]? = some fi ∧
    fi.code = .wasm fn ∧
    ProdL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals))
      (fun n => (ω n).toS) ∧
    ν = fun i => (ω i).lift}

/-- **The canonical CFG closure with divergence**: `cfgEvFunXP` plus `div` after descent chains
and after logged divergence of a body on the machine (`Shape.closeDLog`). -/
def cfgEvFunDXP : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.closeDLog cfgHOpenXP LDLcfg p.1 s p.2

/-- **The productive runs of the CFG closure**: the closure of `cfgHOpenXP` with productive runs
through unbounded recursion and inside one body run on the machine (`Shape.closeInfL`). -/
def cfgEvInfNXP : PInf (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => Shape.closeInfL cfgHOpenXP InfLcfg p.1 s p.2

/-- **The CFG session closure with divergence**: `cfgEvFunXPS` with the divergent behaviours of
`cfgEvFunDXP`. -/
def cfgEvFunDXPS :
    AFun (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  fun s p => cfgEvFunXPS s p ∪ {y | y.2 = .div ∧ (y.1, End.div) ∈ cfgEvFunDXP s p}

/-- **The CFG session triple**: finished and divergent behaviours keeping trap stores, pending
host calls, and productive streams, every Wasm body run on the logged machine. -/
def cfgSessionTriple :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit.{1}) :=
  (cfgEvFunDXPS, cfgEvPendXPS, cfgEvInfNXP)

end Silmaril.Wasm.Cfg.CfgSession
