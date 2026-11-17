module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.CallXP.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLProj
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
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

On untyped code the two machines' stack conventions differ (`ExampleLogged`). The stepwise typed
projection, its exception bridge, and the discharge of `CloseOk` by the canonical host-closing
correspondence remain open (`docs/projects/wasm-cfg.md`).
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

end Silmaril.Wasm.Cfg.MachineL
