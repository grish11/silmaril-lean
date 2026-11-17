module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.CallXP.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLProj
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
import Silmaril.Proofs.Wasm.Cfg.MachineLProjS
import Silmaril.Proofs.Wasm.Cfg.MachineLProjT
import Silmaril.Proofs.Wasm.Cfg.MachineLProjX
import Silmaril.Proofs.Wasm.Cfg.MachineLProjK
import Silmaril.Proofs.Wasm.Cfg.MachineLProjF
public import Silmaril.Wasm.Interp.EHSim.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLProjE
public import Silmaril.Wasm.Abstract.CallXT.Thms
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Interp.EHExt.Thms

@[expose] public section

/-!
# Run-level projection of the logged machine to `MStepC` (H1)

The logged machine `MStepL` (`MachineL`) runs straight-line code by `EvalLXPS`, with open logged
calls and native stack conventions. `MStepC` (`Machine`) runs it by Core region steps, with calls
answered by an oracle and Core's stack conventions. This header projects **whole runs**:

* **`project_sink_closedX`**: a logged run from the CFG entry to a sink (`exit`, `trap`, `raise`)
  is a run of `MStepC` (any profile, no host) from the CFG entry to a sink. Both machines end
  with the same native result: `EndRel` for the logged sink, and `ResOut`/`EndsC` for `MStepC`'s
  sink, so the store and frame are the same unless the end completes a pending tail call.

**This is a run-level corollary, not the stepwise (stuttering) projection.** It composes existing
results: `forward_sink`, `closed_iff_logged`, `CallXP.evalOXP_iff_evalOXE`,
`CallXE.evalOXE_iff_evalOX` and `Bridge.native_machine_closedX`. Its hypotheses are the fragment
those results share. They are stated, and none is claimed to be removable here:

* **The oracle.** Every logged entry is answered by `Machine.closedXOk` (`CloseOk closedXOk`).
  This is the typed closed extended oracle: `StoreChkE tExt` and `Interp.CX closedCallX`, a typed
  entry answered by the closed native semantics. **Host entries are never `CloseOk`**, so a log
  with a host call does not project: `MStepC` has no host answers to forget them into.
* **Call forms.** `xFreeL`: direct `call` only, with no `call_indirect`, `call_ref` or tail calls.
  On such code `EvalOXP` is `EvalOXE`, with no pending tail calls.
* **No exceptions.** `ehFreeL`: no `throw`, `throw_ref` or `try_table`. On such code `EvalOXE` is
  `EvalOX`.
* **Typing.** `Interp.TypedT` for the `tExt` checker, as `native_machine_closedX` needs.

**Control conventions** (toward the stepwise projection). `MStepL` moves between blocks with
native stack conventions, `MStepC` with Core's. They agree when the stacks fit the block types,
which typed code ensures:

* `popN_eq_popL`, `gotoN_eq_goto`: leaving sequences, under `PopFit`;
* `branchN_block`, `branchN_loop`: a branch, when the frame records the label's arity and the
  branch site holds that many values (`topVals_brVals`);
* `armSel_condArm`, `labelArity_eq`: entering an arm, when the stack holds its parameters and the
  block type resolves.

At a function exit they differ: `MStepC` keeps the outer values of every frame left under the
branch-site stack (`brVals_junk`), `MStepL` only the branch-site stack. A stepwise projection
therefore relates exit states up to that prefix.

**The checker invariant** (`CInv`, `MachineLProj.Defs`) discharges these stack-fit hypotheses
along logged runs:

* `cinv_initial`: it holds at the CFG entry when the body passes the function's own check (as
  `StoreChkE` checks it);
* `cinv_step`, `cinv_run`: it is preserved by logged steps and runs, together with the context's
  store invariant (`Ctx.Good`: the functions and tag invariants) and the frame's local count.

Its hypotheses are stated:
* every logged call is an answer of the oracle `C`, which respects arities (`ExposePTyped.ArityResp`:
  from a store agreeing with the context, its answers keep agreeing and return at least the
  callee's results). The arity-fitted closed oracle is one: `TypedCat.arityResp_fitClosed` (for
  `fitP closedCallXP`);
* the body has no `try_table` (`NoTry`).

Each step reads its straight-line code's checked outcome with `ExposePTyped.evalOXP_goodO`: a
fallthrough at the checked height, a branch with at least its label's arity, a return with at least
the result arity.

**Straight-line code** (`seg_runC`). A logged run of `Flat` code whose calls are `CloseOk C`
answers of a sound oracle (`Interp.OracleSoundT`; `Proofs.Bridge.oracleSoundT_closedXOk` gives one
for `closedXOk`) is a region run (`Region.RunC`) with the same oracle, ending as `Bridge.ResOut`
says. The premises are checker facts only, with no Core typing of states:
* the code passes `chkE (ehExt tags)`, which is `tExt`'s check on code without exception forms
  (`chkE_flat_tExt`);
* the store passes `StoreChkE tExt`.

It composes `closed_iff_logged`, `evalOXP_iff_evalOXE`, `evalOXE_iff_evalOX`, `evalOXT_iff_evalOX`
and `Bridge.bridge_fwd`. Under `DirectCalls body` every segment body is `Flat` (`seg_flat`).

**The stepwise projection** (`proj_step`, `proj_runL`, `proj_initial`). On checked states (`CInv`,
`MInv`, `Ctx.Good`), **each logged step is one `MStepC` step**, and the targets are related by
`ProjRel`: equal, or both `exit` with the same store and frame and the `MStepC` stack the logged
one under further values (`brVals`). Runs compose: a logged run from the CFG entry is an `MStepC`
run from the CFG entry, its end related by `ProjRel`. The proof takes the block's whole
straight-line code (segment and plain terminator) to a region run (`plain_runC`, generalizing
`seg_runC`), splits it (`Region.run_split`), and matches the terminator's region run
(`term_run`: a trap, `return`, `br`, `br_if`, a data branch) to the `MStepC` rule; the targets
agree by the invariant (`entry_inv`, `branch_inv`) and the control-agreement lemmas.

Hypotheses, all stated:
* the fragment: no `try_table` (`NoTry`), direct calls only in segment bodies (`DirectCalls`), no
  `throw`/`throw_ref` or extended-call terminators, so no tail calls (`PlainTerms`); a store
  passing `StoreChkE tExt`;
* the oracle `C`: every logged call is `CloseOk C` (host calls never are), and `C` is sound for the
  bridge (`Interp.OracleSoundT`).

The checker invariant needs each segment's checked outcome. `proj_step`, `proj_runL` and
`proj_initial` read it with exceptions on (`ehExt`), from an arity-respecting oracle
(`ExposePTyped.ArityResp`).

**`proj_initial_closedX`** has **no oracle hypothesis**. It reads the checked outcome with `tExt`,
through `Interp.OracleX.evalOXT_goodT`, and the store's functions are kept by the closure
(`XRecursion.closedCallX_funcs`). So for the typed closed extended oracle `closedXOk`:
* a logged run from the CFG entry whose calls are `closedXOk`-answers is an `MStepC closedXOk` run
  from the CFG entry, its end related by `ProjRel`;
* this holds on the shared fragment, for a body passing the function's own `tExt` check, in a
  store whose functions pass `StoreChkE tExt`.

**Straight-line code with pending tail calls** (`flat_runP`). A native run with pending tail
calls (`CallXP.EvalOXP C`) of code whose every instruction lifts to a single tree
(`liftInstr i = .op i []`: no `block`, `loop`, `if` or `try_table`; direct, indirect and
reference calls, the tail calls, `throw`, `throw_ref`, branches, `return`, `unreachable` and
every other flat instruction are allowed) is a region run (`Region.RunC`) of the code with the
same oracle, ending as `ResOutP` (`MachineLProj.Defs`) says: a flow in the same store and frame,
related by `Bridge.FlowRel` (including `throw`, and a native trap from an unresolved tail call
as a region pending tail call of null); a pending tail call `tail a args n` as the region's
pending tail call `.tail W a c` (`c` a `return_call_ref` form, not answered), in the same store
and frame, with `W` the whole Core stack below the callee, `args` its top values as many as the
callee's parameters, and `n` the callee's result count. Hypotheses, all stated:
* the code passes the check with exceptions on, `chkE (ehExt Γ.tags)`, at the stack's height;
* the oracle respects arities (`ExposePTyped.ArityResp Γ C`) and the initial store agrees with
  `Γ` (`Γ.Good s`). They are used to check each instruction's continuation at the height the
  instruction leaves (`ExposePTyped.evalOXP_goodO` on the instruction): a call's answer keeps
  the store's functions and returns at least the callee's result count. No soundness of `C`
  (`Interp.OracleSoundT`) and no `StoreChkE` is assumed: the region run answers the same calls
  by the same `C`.

**The stepwise projection over the pending, exception-aware semantics** (`proj_stepE`,
`proj_runLE`, `proj_initialE`). The same statement as `proj_step`, with the segment bridge
`flat_runP` (`EvalOXP`, `ehExt`). The hypotheses are only:
* bodies without `try_table` (`NoTry`);
* an arity-respecting oracle (`ArityResp Γ C`), with `CloseOk C` logs and `Ctx.Good` stores.

No restriction on call forms (`call_indirect`, `call_ref`), on terminators (`throw`,
`throw_ref`, tail calls) or on the store's checker. A `throw`/`throw_ref` terminator is
`MStepC.raise`, and a tail call of null is `MStepC.tailNull`. An answered tail call is an end of
the logged run (`TailL`), not a step. **`proj_tailE`**, **`proj_tail_initialE`**: a run ending in a
pending tail call whose answer is a `CloseOk C` entry is an `MStepC` run whose last step is
`MStepC.tail`, which makes the call through `C` and replaces the function's frame. The run ends at
the sink the answer stands for (`tailSink`: the returned values at `exit`, the exception at
`raise`, or `trap`). The handler case (`try_table`) is separate (`docs/projects/wasm-cfg.md`).

**Handlers** (`cinv_stepE`, `cinv_runE`, `proj_stepK`, `proj_runLK`, `proj_initialK`,
`proj_tail_initialK`). The same theorems **without `NoTry`**: `try_table` frames are entered,
left, branched across, and catch.
* The checker invariant records each `try_table` frame's clause check (`ChkF`).
* A caught exception branches to the clause's label with at least its arity (`catch_arity`, from
  `Interp.catches_count` under the tag invariants of `Ctx.Good`).
* Catches map to `MStepC.catch_`/`bodyCatch` (block targets equal) and to
  `MStepC.catchOut`/`bodyCatchOut` (exits, related by `ProjRel`'s junk); uncaught exceptions
  pass every handler as in `MStepC.raise`/`bodyRaise`.

The hypotheses are now only an arity-respecting oracle (`ArityResp Γ C`) with `CloseOk C` logs,
`Ctx.Good` stores, and the body's own `chkE (ehExt tags)` check. That is every call form and every
structured instruction, exceptions on.

**`tail_fit_initialK`**: under the same hypotheses, the pending tail call at the end of a logged run
from the CFG entry (`TailL`) passes exactly its callee's parameter count, and its result count is
the callee's (from `flat_runP`'s `ResOutP`). So its answer by a closure restricted to fitting calls
(`TypedCat.fitP`) is an answer of that restriction (`MachineLClose`).

On untyped code the two machines' stack conventions differ (`ExampleLogged`). For host-free
behaviours of the session closure, `CloseOk (fitP closedCallXP)` is discharged in
`Silmaril.Wasm.Cfg.MachineLClose`; logs with host events remain open
(`docs/projects/wasm-cfg.md`).
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

/-- **A logged run to a sink is an `MStepC` run to a sink with the same native result**: logs
answered by the typed closed extended oracle, typed code, direct calls only, no exceptions. -/
theorem project_sink_closedX (P : Numerics.Profile) {body : Expr} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {st : MState H} (h : MRunL body (initial body s f) l st)
    (hs : st.node.IsSink) (hl : ∀ e ∈ l, CloseOk closedXOk e)
    (ht : Interp.TypedT s f [] (liftInstrs body))
    (hx : Abstract.CallX.xFreeL (liftInstrs body) = true)
    (he : Abstract.CallXE.ehFreeL (liftInstrs body) = true) :
    ∃ (s₂ : Store H) (f₂ : Frame) (fl : Flow) (s' : Store H) (f' : Frame) (o : Region.Out)
      (st' : MState H), EndRel st (s₂, f₂, .flow fl) ∧ ResOut closedXOk s' f' o (s₂, f₂, fl) ∧
      Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk body) (initial body s f) st' ∧
      EndsC closedXOk st' s' f' o :=
  Proofs.MachineLProj.project_sink_closedX P h hs hl ht hx he

/-! ## Control conventions -/

/-- **Native frame popping is Core's** on fitting stacks. -/
theorem popN_eq_popL (f : Frame) (k : Nat) (ls : List LFrame) (stk : List Val)
    (h : PopFit f k ls stk) : popN f k ls stk = some (popL k ls stk) :=
  Proofs.MachineLProjC.popN_eq_popL f k ls stk h

/-- **Native moves are Core's** on fitting stacks. -/
theorem gotoN_eq_goto {t : Target} {d : Nat} {ls : List LFrame} {stk : List Val} {s : Store H}
    {f : Frame} (h : PopFit f (d - depthT t) ls stk) :
    gotoN t d ls stk s f = some (goto t d ls stk s f) :=
  Proofs.MachineLProjC.gotoN_eq_goto h

/-- The values a Core branch carries are the branch-site stack over the left frames' values. -/
theorem brVals_junk (k : Nat) (ls : List LFrame) (stk : List Val) :
    ∃ junk, brVals k ls stk = junk ++ stk :=
  Proofs.MachineLProjC.brVals_junk k ls stk

/-- The top values a branch keeps, native and Core, when the branch site holds them. -/
theorem topVals_brVals {n k : Nat} {ls : List LFrame} {N : List Val} (h : n ≤ N.length) :
    topVals n (brVals k ls N.reverse) = (N.take n).reverse :=
  Proofs.MachineLProjC.topVals_brVals h

/-- **A branch to a `block`, `if` or `try_table` label**, native and Core. -/
theorem branchN_block {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {np nr : Nat} (hloop : L.loop = false)
    (har : Binaryen.arity f L.bt = some (np, nr)) (hLa : L.arity = nr) (hN : nr ≤ N.length) :
    branchN body b ls k L N s f =
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - (k + 1)) (ls.drop (k + 1))
        (L.outer ++ topVals L.arity (brVals k ls N.reverse)) s f :=
  Proofs.MachineLProjC.branchN_block hloop har hLa hN

/-- **A branch to a `loop` label**, native and Core. -/
theorem branchN_loop {body : Expr} {b : BlockId} {ls : List LFrame} {k : Nat} {L : LFrame}
    {N : List Val} {s : Store H} {f : Frame} {np nr : Nat} (hloop : L.loop = true)
    (har : Binaryen.arity f L.bt = some (np, nr)) (hLa : L.arity = np) (hN : np ≤ N.length) :
    branchN body b ls k L N s f =
      gotoN ((labels body b.seq).getD k .invalid) (b.seq.length - k) (L :: ls.drop (k + 1))
        (topVals L.arity (brVals k ls N.reverse)) s f :=
  Proofs.MachineLProjC.branchN_loop hloop har hLa hN

/-- **Entering an arm**: the native split (`ArmSel`) is Core's (`CondArm`). -/
theorem armSel_condArm {i : Instr} {V V' : List Val} {a np : Nat} (h : ArmSel i V a V')
    (hnp : np ≤ V'.length) :
    CondArm i V.reverse a (V'.drop np).reverse (V'.take np).reverse ∧
      (V'.take np).reverse.length = np :=
  Proofs.MachineLProjC.armSel_condArm h hnp

/-- **The frame an arm entry pushes** has the same label arity, native and Core. -/
theorem labelArity_eq {f : Frame} {bt : BlockType} {t₁ t₂ : List Validation.CValType}
    {np nr : Nat} (loop : Bool) (hbt : f.module.blockType? bt = some (t₁, t₂))
    (har : Binaryen.arity f bt = some (np, nr)) :
    labelArity loop t₁ t₂ = if loop then np else nr :=
  Proofs.MachineLProjC.labelArity_eq loop hbt har

/-! ## The checker invariant -/

open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.ExposePStruct

/-- **The checker invariant at the CFG entry**, from the function's own check. -/
theorem cinv_initial {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hf : f.module = mi)
    (hchk : endsAt (chkE ext F mi nl ret [ret] (some 0) (liftInstrs body)) ret = true) :
    CInv ext F mi nl ret body (initial body s f) :=
  Proofs.MachineLProjI.cinv_initial hf hchk

/-- **The checker invariant is preserved by logged steps** whose calls are answers of an
arity-respecting oracle, on bodies without `try_table`. -/
theorem cinv_step {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' :=
  Proofs.MachineLProjI.cinv_step hC hNT hs hl hok hg hn hI

/-- **The checker invariant along logged runs.** -/
theorem cinv_run {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' :=
  Proofs.MachineLProjI.cinv_run hC hNT h hl hok hg hn hI

/-! ## Straight-line code -/

/-- **Off the exception forms the check is `tExt`'s.** -/
theorem chkE_flat_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {is : List Instr} (oh : Option Nat)
    (h : ∀ i ∈ is, Cfg.isTerminator i = false) :
    chkE (ehExt tags) F mi nl ret labels oh (liftInstrs is) =
      chkE tExt F mi nl ret labels oh (liftInstrs is) :=
  Proofs.MachineLProjS.chkE_flat_tExt oh h

/-- **Segment bodies are straight-line code** when the body makes direct calls only. -/
theorem seg_flat {body : Expr} (hD : DirectCalls body) {p : List SeqStep} {c : List Instr}
    {i : Nat} {sg : Segment} (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) :
    Flat sg.body :=
  Proofs.MachineLProjS.seg_flat hD hc hsg

/-- **Logged straight-line code is a region run** with the same oracle, ending as `ResOut`
says. -/
theorem seg_runC {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H}
    {C : Abstract.CallRel H} (hC : OracleSoundT P₀ host₀ C) {tags : List TagInst}
    {is : List Instr} (hflat : Flat is) {s : Store H} {f : Frame} {N : List Val}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut}
    (hr : Abstract.EvalLXPS s f N (liftInstrs is) l r) (hl : ∀ e ∈ l, CloseOk C e)
    (hS : StoreChkE tExt s.funcs) {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (liftInstrs is) = some out) :
    ∃ (s₂ : Store H) (f₂ : Frame) (fl : Flow), r = (s₂, f₂, .flow fl) ∧
      ∃ s' f' o, Region.RunC P host C s f N.reverse (expression is) s' f' o ∧
        Bridge.ResOut C s' f' o (s₂, f₂, fl) :=
  Proofs.MachineLProjS.seg_runC hC hflat hr hl hS hchk

/-! ## The stepwise projection -/

/-- **A logged step projects to one `MStepC` step** (checked states, the shared fragment). -/
theorem proj_step {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H}
    {C : Abstract.CallRel H} (hC : OracleSoundT P₀ host₀ C) {Γ : Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hPT : PlainTerms body) (hS : StoreChkE tExt Γ.funcs) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjT.proj_step hC hA hNT hD hPT hS hs hl hok hg hn hI

/-- **A logged run projects to an `MStepC` run**, step by step (checked states, the shared
fragment). -/
theorem proj_runL {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H}
    {C : Abstract.CallRel H} (hC : OracleSoundT P₀ host₀ C) {Γ : Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hPT : PlainTerms body) (hS : StoreChkE tExt Γ.funcs) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjT.proj_runL hC hA hNT hD hPT hS h hl hok hg hn hI

/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry**, for a body
passing the function's own check. -/
theorem proj_initial {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H}
    {C : Abstract.CallRel H} (hC : OracleSoundT P₀ host₀ C) {Γ : Ctx H} (hA : ArityResp Γ C)
    {ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body)
    (hS : StoreChkE tExt Γ.funcs) {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧
      ProjRel st' stC :=
  Proofs.MachineLProjT.proj_initial hC hA hNT hD hPT hS hg hchk h hl

/-- **The closed instance, no oracle hypothesis**: a logged run from the CFG entry whose calls
are answers of the typed closed extended oracle `closedXOk` is an `MStepC` run with `closedXOk`
from the CFG entry, its end related by `ProjRel`, on the shared fragment, for a body passing the
function's own `tExt` check in a store whose functions pass it. -/
theorem proj_initial_closedX {P : Numerics.Profile} {host : HostSemantics H}
    {F : List (FuncInst H)} (hS : StoreChkE tExt F) {ret : Nat} {body : Expr}
    (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body) {s : Store H} {f : Frame}
    (hs : s.funcs = F)
    (hchk : endsAt (chkE tExt F f.module f.locals.length ret [ret] (some 0) (liftInstrs body)) ret =
      true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk closedXOk e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host closedXOk body) (initial body s f) stC ∧
      ProjRel st' stC :=
  Proofs.MachineLProjT.proj_initial_closedX hS hNT hD hPT hs hchk h hl

/-! ## Straight-line code with pending tail calls -/

/-- **Straight-line code with pending tail calls is a region run** with the same oracle, ending
as `ResOutP` says, for an arity-respecting oracle from a store agreeing with `Γ`, on code passing
the check with exceptions on. -/
theorem flat_runP {P : Numerics.Profile} {host : HostSemantics H} {Γ : Ctx H}
    {C : Abstract.CallRel H} (hA : ArityResp Γ C) {is : List Instr}
    (hflat : ∀ i ∈ is, liftInstr i = .op i []) {s : Store H} {f : Frame} {N : List Val}
    {r : Store H × Frame × Abstract.CallXP.POut}
    (d : Abstract.CallXP.EvalOXP C s f N (liftInstrs is) r) (hg : Γ.Good s)
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (liftInstrs is) = some out) :
    ∃ s' f' o, Region.RunC P host C s f N.reverse (expression is) s' f' o ∧ ResOutP s' f' o r :=
  Proofs.MachineLProjE.flat_runP hA hflat d hg hchk

/-! ## The stepwise projection, exceptions on -/

/-- **A logged step projects to one `MStepC` step** (exceptions on, every call form, bodies
without `try_table`, an arity-respecting oracle). -/
theorem proj_stepE {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    (hNT : NoTry body) {st st' : MState H} {l : List (Abstract.SCall H)}
    (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjX.proj_stepE hA hNT hs hl hok hg hn hI

/-- **A logged run projects to an `MStepC` run**, step by step (exceptions on). -/
theorem proj_runLE {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    (hNT : NoTry body) {st st' : MState H} {l : List (Abstract.SCall H)}
    (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjX.proj_runLE hA hNT h hl hok hg hn hI

/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry**
(exceptions on), for a body passing the function's own check. -/
theorem proj_initialE {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {ret : Nat} {body : Expr} (hNT : NoTry body)
    {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧
      ProjRel st' stC :=
  Proofs.MachineLProjX.proj_initialE hA hNT hg hchk h hl

/-- **An answered tail call projects to `MStepC.tail`** (frame replacement), to the sink the
answer stands for. -/
theorem proj_tailE {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    {st : MState H} {l : List (Abstract.SCall H)} {s₁ s₂ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (ht : TailL body st l (s₁, f₁, .tail a args n)) (hl : ∀ e ∈ l, CloseOk C e)
    (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) (hg : Γ.Good st.store)
    (hn : st.frame.locals.length = nl) (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    MStepC P host C body st (tailSink b s₂ f₁) :=
  Proofs.MachineLProjX.proj_tailE hA ht hl he hg hn hI

/-- **A logged run from the CFG entry ending in an answered tail call** is an `MStepC` run from
the CFG entry to the sink the answer stands for. -/
theorem proj_tail_initialE {P : Numerics.Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} {Γ : Ctx H} (hA : ArityResp Γ C) {ret : Nat} {body : Expr}
    (hNT : NoTry body) {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ s₂ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (h : MRunL body (initial body s f) l st) (ht : TailL body st l' (s₁, f₁, .tail a args n))
    (hl : ∀ e ∈ l ++ l', CloseOk C e) (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) :
    Relation.ReflTransGen (MStepC P host C body) (initial body s f) (tailSink b s₂ f₁) :=
  Proofs.MachineLProjX.proj_tail_initialE hA hNT hg hchk h ht hl he

/-! ## Handlers -/

/-- **The checker invariant is preserved by logged steps**, `try_table` included. -/
theorem cinv_stepE {C : Abstract.CallRel H} {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st st' : MState H} {l : List (Abstract.SCall H)}
    (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' :=
  Proofs.MachineLProjK.cinv_stepE hA hs hl hok hg hn hI

/-- **The checker invariant along logged runs**, `try_table` included. -/
theorem cinv_runE {C : Abstract.CallRel H} {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st st' : MState H} {l : List (Abstract.SCall H)}
    (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    Γ.Good st'.store ∧ st'.frame.locals.length = nl ∧
      CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st' :=
  Proofs.MachineLProjK.cinv_runE hA h hl hok hg hn hI

/-- **A logged step projects to one `MStepC` step**: every call form and structured instruction,
exceptions on. -/
theorem proj_stepK {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    {st st' : MState H} {l : List (Abstract.SCall H)} (hs : MStepL body st l st')
    (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st) (hg : Γ.Good st.store)
    (hn : st.frame.locals.length = nl) (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjK.proj_stepK hA hs hl hok hg hn hI

/-- **A logged run projects to an `MStepC` run**, step by step: every call form and structured
instruction, exceptions on. -/
theorem proj_runLK {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    {st st' : MState H} {l : List (Abstract.SCall H)} (h : MRunL body st l st')
    (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st) (hg : Γ.Good st.store)
    (hn : st.frame.locals.length = nl) (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC :=
  Proofs.MachineLProjK.proj_runLK hA h hl hok hg hn hI

/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry**: every
call form and structured instruction, exceptions on. -/
theorem proj_initialK {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
    {Γ : Ctx H} (hA : ArityResp Γ C) {ret : Nat} {body : Expr} {s : Store H} {f : Frame}
    (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧
      ProjRel st' stC :=
  Proofs.MachineLProjK.proj_initialK hA hg hchk h hl

/-- **A logged run from the CFG entry ending in an answered tail call** is an `MStepC` run to the
sink the answer stands for: every call form and structured instruction, exceptions on. -/
theorem proj_tail_initialK {P : Numerics.Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} {Γ : Ctx H} (hA : ArityResp Γ C) {ret : Nat} {body : Expr}
    {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ s₂ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    (h : MRunL body (initial body s f) l st) (ht : TailL body st l' (s₁, f₁, .tail a args n))
    (hl : ∀ e ∈ l ++ l', CloseOk C e) (he : CloseOk C (Abstract.SCall.mk a args s₁ b s₂)) :
    Relation.ReflTransGen (MStepC P host C body) (initial body s f) (tailSink b s₂ f₁) :=
  Proofs.MachineLProjK.proj_tail_initialK hA hg hchk h ht hl he

/-- **A pending tail call at the end of a checked logged run fits its callee**: the callee of the
store the call leaves has a function type `(ps, rs)`, the call passes exactly `ps.length`
arguments, and its result count is `rs.length`. -/
theorem tail_fit_initialK {C : Abstract.CallRel H} {Γ : Ctx H} (hA : ArityResp Γ C) {ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} (h : MRunL body (initial body s f) l st)
    (ht : TailL body st l' (s₁, f₁, .tail a args n)) (hl : ∀ e ∈ l ++ l', CloseOk C e) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s₁.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ args.length = ps.length ∧
      n = rs.length :=
  Proofs.MachineLProjF.tail_fit_initialK hA hg hchk h ht hl

end Silmaril.Wasm.Cfg.MachineL
