module

public import Silmaril.Wasm.Cfg.Bridge.Defs
public import Silmaril.Wasm.Cfg.BridgeBwd.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Interp.OracleX.Thms
public import Silmaril.Wasm.Cfg.MachineClosedX.Defs
import Silmaril.Proofs.Wasm.Cfg.BridgeBwdTree
import Silmaril.Proofs.Wasm.Cfg.BridgeBwdTail

@[expose] public section

/-!
# The backward bridge from the region semantics to extended native trees

The converse of `Cfg.Bridge.bridge_fwd`, built in bounded steps. Proofs are in
`Silmaril.Proofs.Wasm.Cfg.BridgeBwd`.

* **`flat_bwd`** (deterministic profile `SingleThreaded.profile o`, any host and any oracle): a
  region run (`Region.RunC`) of a checked (`Interp.flatChk`), typed (`Sim.ContextTyped`) flat
  instruction other than a call is its native `evalFlat` result: the same store and frame, and
  `FlowRel` flows. This is the flat case of the backward bridge. It reuses HostEval's flat
  completeness (`Abstract.flat_complete`, a Core run of the instruction to a stuck final form is
  the `evalFlat` result) for the instructions the region runs by Core reduction, and computes
  constants, `br`, `br_if`, `br_table` and `return` on both sides; the check excludes every other
  region rule.

* **`bridge_bwd_tailFree`** (deterministic profile, no host): with an oracle sound for the
  tail-aware check that keeps typing (`Interp.OracleSoundT`, `CallXT.KeepsTy`), a region run of
  the lowering of typed trees (`Interp.TypedT`) without tail calls (`tailFreeL`; direct, indirect
  and reference calls are included, each answered by the same oracle after the same resolution)
  is a native `EvalOX` run with **the same oracle**, ending as `ResOut` says. `bridge_bwd` is the
  case of trees without extended call forms (`CallX.xFreeL`). This is the converse of `bridge_fwd` on that
  fragment. By induction on the size of the trees: sequencing (`run_split`), operators through
  their arguments then `flat_bwd` or the oracle's call entry, blocks and `if` arms through their
  label, and loops by induction on their region run, re-entering at every branch back to the
  loop. Typing at each node comes from Interp's typed lemmas (`site_typedT`, `cont_typedT`,
  `loop_back_typedT`, `arm_typedT`, …); arities from the checker (`body_facts`, `if_facts`).
* **`bridge_bwd_closedX`**, **`bridge_bwd_tailFree_closedX`**: the instances with the typed
  closed extended oracle `closedXOk`, with no oracle hypothesis.

* **`bridge_bwd_nonTail`**, **`bridge_bwd_nonTail_closedX`**: every typed tree, tail calls
  included, provided the region outcome is not a pending tail call of a function. A
  `return_call_ref` on null and a `return_call_indirect` without a callee end the region in a trap
  or a pending tail call of null, and the native evaluator traps (`EvalOX.tailRes`). For
  `return_call_indirect` the region runs `table.get; ref.cast` by Core reduction; at the
  deterministic profile without host these runs are forced (unique host-free normal forms), so
  they resolve the index as `CallRes.IndRes` does.

* **`bridge_bwd_tail`**, **`bridge_bwd_tail_closedX`**: a region run ending in a pending tail call
  of a function (`Region.Out.tail W a c`, answered only at the frame) corresponds, for **every**
  answer of the oracle to that call (`ResOut … (.tail W a c) r`), to a native run to `r`: the
  native evaluator makes the call at once (`EvalOX.tail`). The callee's parameters are on `W`
  (from typing at the call site), so the values an enclosing label puts under `W` do not change
  the call's arguments.
* **`bridge_bwd_answered`**, **`bridge_bwd_answered_closedX`**: the two together, as an existence
  statement: if the outcome is not a pending tail call, or the oracle answers it, the region run
  is a native run with the same oracle, ending as `ResOut` says. Without an answer to a pending
  tail call there is no native result, so the hypothesis cannot be dropped.
-/

namespace Silmaril.Wasm.Cfg.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

/-- **A region run of a checked, typed flat instruction is its `evalFlat` result**
(deterministic profile, any host and oracle). -/
theorem flat_bwd {o : SingleThreaded.GrowOracle} {host : HostSemantics H}
    {C : Abstract.CallRel H} {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat} {oc : Option Nat}
    {out : Region.Out} (hi : ∀ x, i ≠ .call x)
    (hc : Interp.flatChk F mi f.locals.length ret labels stk.length i = some oc)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain i]⟩)
    (h : Region.RunC (SingleThreaded.profile o) host C s f stk.reverse [.plain i] s' f' out) :
    ∃ fl, evalFlat s f stk i = some (s', f', fl) ∧ FlowRel fl out :=
  Proofs.Bridge.flat_bwd hi hc ht h

/-- **The backward bridge, without extended calls**: a region run of the lowering of typed trees
without `call_indirect`, `call_ref` or tail calls is a native run with the same oracle, ending as
`ResOut` says (deterministic profile, no host, an oracle sound for the tail-aware check that keeps
typing). -/
theorem bridge_bwd {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    {C : Abstract.CallRel H} (hC : Interp.OracleSoundT P₀ Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {out : Region.Out} (ht : Interp.TypedT s f stk es)
    (hx : Abstract.CallX.xFreeL es = true)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX C s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX C s f stk es r ∧ ResOut C s' f' out r :=
  Proofs.Bridge.bwdL_all hC hCk es ht (.inl (Proofs.Bridge.tailFreeL_of_xFreeL es hx)) h

/-- **The backward bridge, without tail calls**: a region run of the lowering of typed trees
without tail calls (direct, indirect and reference calls included) is a native run with the same
oracle, ending as `ResOut` says. -/
theorem bridge_bwd_tailFree {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    {C : Abstract.CallRel H} (hC : Interp.OracleSoundT P₀ Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {out : Region.Out} (ht : Interp.TypedT s f stk es)
    (hx : tailFreeL es = true)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX C s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX C s f stk es r ∧ ResOut C s' f' out r :=
  Proofs.Bridge.bwdL_all hC hCk es ht (.inl hx) h

/-- `bridge_bwd_tailFree` for the typed closed extended oracle (no oracle hypothesis). -/
theorem bridge_bwd_tailFree_closedX {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {f f' : Frame} {stk : List Val} {es : List BExpr} {out : Region.Out}
    (ht : Interp.TypedT s f stk es) (hx : tailFreeL es = true)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX Machine.closedXOk s f stk es r ∧ ResOut Machine.closedXOk s' f' out r :=
  bridge_bwd_tailFree (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht hx h

/-- **The backward bridge for the typed closed extended oracle** (no oracle hypothesis). -/
theorem bridge_bwd_closedX {o : SingleThreaded.GrowOracle} {s s' : Store H} {f f' : Frame}
    {stk : List Val} {es : List BExpr} {out : Region.Out} (ht : Interp.TypedT s f stk es)
    (hx : Abstract.CallX.xFreeL es = true)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX Machine.closedXOk s f stk es r ∧ ResOut Machine.closedXOk s' f' out r :=
  bridge_bwd (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht hx h

/-- **The backward bridge for every outcome but a pending tail call of a function**: a region run
of the lowering of typed trees (tail calls included) whose outcome is not `Out.tail` is a native
run with the same oracle, ending as `ResOut` says. -/
theorem bridge_bwd_nonTail {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    {C : Abstract.CallRel H} (hC : Interp.OracleSoundT P₀ Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {out : Region.Out} (ht : Interp.TypedT s f stk es)
    (hnt : ∀ W a c, out ≠ .tail W a c)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX C s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX C s f stk es r ∧ ResOut C s' f' out r :=
  Proofs.Bridge.bwdL_all hC hCk es ht (.inr hnt) h

/-- `bridge_bwd_nonTail` for the typed closed extended oracle (no oracle hypothesis). -/
theorem bridge_bwd_nonTail_closedX {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {f f' : Frame} {stk : List Val} {es : List BExpr} {out : Region.Out}
    (ht : Interp.TypedT s f stk es) (hnt : ∀ W a c, out ≠ .tail W a c)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX Machine.closedXOk s f stk es r ∧ ResOut Machine.closedXOk s' f' out r :=
  bridge_bwd_nonTail (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht hnt h

/-- **The backward bridge for a pending tail call**: for every answer of the oracle to the
pending call, the trees run natively to the result it gives. -/
theorem bridge_bwd_tail {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    {C : Abstract.CallRel H} (hC : Interp.OracleSoundT P₀ Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s s' : Store H} {f f' : Frame} {stk W : List Val}
    {es : List BExpr} {a : Nat} {c : Admin} (ht : Interp.TypedT s f stk es)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX C s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' (.tail W a c))
    {r : Store H × Frame × Flow} (hr : ResOut C s' f' (.tail W a c) r) :
    Abstract.CallX.EvalOX C s f stk es r :=
  (Proofs.Bridge.bwdTL_all hC hCk es ht h).2 r hr

/-- `bridge_bwd_tail` for the typed closed extended oracle (no oracle hypothesis). -/
theorem bridge_bwd_tail_closedX {o : SingleThreaded.GrowOracle} {s s' : Store H} {f f' : Frame}
    {stk W : List Val} {es : List BExpr} {a : Nat} {c : Admin} (ht : Interp.TypedT s f stk es)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' (.tail W a c))
    {r : Store H × Frame × Flow} (hr : ResOut Machine.closedXOk s' f' (.tail W a c) r) :
    Abstract.CallX.EvalOX Machine.closedXOk s f stk es r :=
  bridge_bwd_tail (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht h hr

/-- **The backward bridge, as an existence statement**: if the region outcome is not a pending
tail call, or the oracle answers it, the region run of typed trees is a native run with the same
oracle, ending as `ResOut` says. -/
theorem bridge_bwd_answered {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    {C : Abstract.CallRel H} (hC : Interp.OracleSoundT P₀ Interp.noHostX C)
    (hCk : Abstract.CallXT.KeepsTy C) {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {out : Region.Out} (ht : Interp.TypedT s f stk es)
    (hans : (∀ W a c, out ≠ .tail W a c) ∨ ∃ r, ResOut C s' f' out r)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX C s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX C s f stk es r ∧ ResOut C s' f' out r := by
  by_cases hnt : ∀ W a c, out ≠ .tail W a c
  · exact bridge_bwd_nonTail hC hCk ht hnt h
  · simp only [not_forall, not_not] at hnt
    obtain ⟨W, a, c, rfl⟩ := hnt
    obtain ⟨r, hr⟩ := hans.resolve_left (fun hn => hn W a c rfl)
    exact ⟨r, bridge_bwd_tail hC hCk ht h hr, hr⟩

/-- `bridge_bwd_answered` for the typed closed extended oracle (no oracle hypothesis). -/
theorem bridge_bwd_answered_closedX {o : SingleThreaded.GrowOracle} {s s' : Store H}
    {f f' : Frame} {stk : List Val} {es : List BExpr} {out : Region.Out}
    (ht : Interp.TypedT s f stk es)
    (hans : (∀ W a c, out ≠ .tail W a c) ∨ ∃ r, ResOut Machine.closedXOk s' f' out r)
    (h : Region.RunC (SingleThreaded.profile o) Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' out) :
    ∃ r, Abstract.CallX.EvalOX Machine.closedXOk s f stk es r ∧ ResOut Machine.closedXOk s' f' out r :=
  bridge_bwd_answered (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht hans h

end Silmaril.Wasm.Cfg.Bridge
