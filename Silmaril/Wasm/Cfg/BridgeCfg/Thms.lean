module

public import Silmaril.Wasm.Cfg.BridgeBwd.Thms
public import Silmaril.Wasm.Cfg.Bridge.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
import Silmaril.Proofs.Wasm.Cfg.BridgeCfg

@[expose] public section

/-!
# The block-CFG machine against native trees

The machine runs a function body on its extracted block CFG (`Cfg.Machine.MStepC`, calls
answered by an oracle `C`); the native evaluator runs the folded trees (`CallX.EvalOX`, the same
oracle). Composing the machine's region soundness and completeness (`run_sound_initialC`,
`run_complete_initialC`, `run_complete_tail_initialC`) with the bridge in both directions
(`bridge_fwd`, `bridge_bwd`):

* **`machine_native`** (deterministic profile, no host, an oracle sound for the tail-aware check
  that keeps typing): a machine run from the CFG entry of the lowering of typed trees without
  extended calls (`CallX.xFreeL`) to a sink is a native run of the trees from the empty stack
  with the same oracle, ending as the sink completes (`EndsC`) and `ResOut` relate.
* **`native_machine`** (any profile and host for the machine; an oracle sound for the tail-aware
  check): a typed, checked native run from the empty stack has a region outcome `o` related to
  its result by `ResOut`, and, unless `o` is a branch out of the body, a machine run from the
  CFG entry to a sink completing `o` (`EndsC`). Pending tail calls are completed by the oracle
  answer that `ResOut` carries.
* `machine_native_closedX`, `native_machine_closedX`: the instances with the typed closed
  extended oracle `closedXOk`, with no oracle hypothesis.

Scope: the machine-to-native direction excludes `call_indirect`, `call_ref` and tail calls (the
open part of the backward bridge). These are statements about the CFG as an executable semantics
of the body, at its region outcomes; they are not statements about the plain extracted graph's
infeasible paths, which stay an over-approximation.
-/

namespace Silmaril.Wasm.Cfg.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Cfg.Machine

variable {H : Type} {C : Abstract.CallRel H}

/-- **Machine runs are native runs** (trees without extended calls, deterministic profile). -/
theorem machine_native {o : SingleThreaded.GrowOracle} {P₀ : Numerics.Profile}
    (hC : Interp.OracleSoundT P₀ Interp.noHostX C) (hCk : Abstract.CallXT.KeepsTy C)
    {s : Store H} {f : Frame} {es : List BExpr} {st' : MState H}
    (ht : Interp.TypedT s f [] es) (hx : Abstract.CallX.xFreeL es = true)
    (h : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) Interp.noHostX C
      (BExpr.lowerList es)) (initial (BExpr.lowerList es) s f) st')
    (hs : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC C st' s₂ f₂ out ∧ Abstract.CallX.EvalOX C s f [] es r ∧
      ResOut C s₂ f₂ out r :=
  Proofs.BridgeCfg.machine_native hC hCk ht hx h hs

/-- **Native runs are machine runs**, unless the body branches out of itself. -/
theorem native_machine {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) (P : Numerics.Profile) (host : HostSemantics H)
    {s : Store H} {f : Frame} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : Abstract.CallXT.EvalOXT C s f [] es r) {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChkE Interp.tExt s.funcs)
    (hchk : Interp.chkE Interp.tExt s.funcs f.module f.locals.length ret labels (some 0) es =
      some out) :
    ∃ s' f' o, ResOut C s' f' o r ∧
      ((∃ k us, o = .br k us) ∨
        ∃ st', Relation.ReflTransGen (MStepC P host C (BExpr.lowerList es))
          (initial (BExpr.lowerList es) s f) st' ∧ EndsC C st' s' f' o) :=
  Proofs.BridgeCfg.native_machine hC P host h hS hchk

/-- `machine_native` for the typed closed extended oracle (no oracle hypothesis). -/
theorem machine_native_closedX {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {es : List BExpr} {st' : MState H}
    (ht : Interp.TypedT s f [] es) (hx : Abstract.CallX.xFreeL es = true)
    (h : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) Interp.noHostX closedXOk
      (BExpr.lowerList es)) (initial (BExpr.lowerList es) s f) st')
    (hs : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC closedXOk st' s₂ f₂ out ∧ Abstract.CallX.EvalOX closedXOk s f [] es r ∧
      ResOut closedXOk s₂ f₂ out r :=
  Proofs.BridgeCfg.machine_native_closedX ht hx h hs

/-- `native_machine` for the typed closed extended oracle (no oracle hypothesis). -/
theorem native_machine_closedX (P : Numerics.Profile) {s : Store H} {f : Frame}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : Abstract.CallX.EvalOX closedXOk s f [] es r)
    (ht : Interp.TypedT s f [] es) :
    ∃ s' f' o, ResOut closedXOk s' f' o r ∧
      ((∃ k us, o = .br k us) ∨
        ∃ st', Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk (BExpr.lowerList es))
          (initial (BExpr.lowerList es) s f) st' ∧ EndsC closedXOk st' s' f' o) :=
  Proofs.BridgeCfg.native_machine_closedX P h ht

end Silmaril.Wasm.Cfg.Bridge
