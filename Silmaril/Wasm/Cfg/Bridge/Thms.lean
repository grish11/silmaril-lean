module

public import Silmaril.Wasm.Cfg.Bridge.Defs
public import Silmaril.Wasm.Cfg.MachineClosedX.Defs
public import Silmaril.Wasm.Interp.OracleX.Thms
public import Silmaril.Wasm.Abstract.CallXT.Defs
import Silmaril.Proofs.Wasm.Cfg.Bridge

@[expose] public section

/-!
# The bridge from extended native trees to the region semantics (forward)

**`bridge_fwd`**: every typed (`CallXT.EvalOXT`), checked (`Interp.chkE Interp.tExt`, on a
`tExt`-checked store) native run of trees `es` with an oracle `C` sound for the tail-aware
check (`Interp.OracleSoundT`) is a region run (`Region.RunC`, any profile and host) of their
lowering with **the same oracle**, from the reversed stack, ending as `ResOut` says:

* the same store and frame, and `FlowRel` flows, for values, branches (the region also carries
  the enclosing labels' values), returns, traps and exceptions;
* a resolved tail call ends the region in a **pending** tail call (`Out.tail`), and the native
  result is the oracle's answer to it on the top arguments (`tailFlow` of the callee's flow, in
  the callee's store and the caller's frame), as `Machine.EndsC` completes it at the frame;
* an unresolved tail call traps natively; the region traps too, or ends in a pending tail call
  of null (`Out.tailNull`), which traps at the frame.

Direct, indirect (`CallRes.IndRes`) and reference calls are answered by the same oracle on both
sides. The checker facts are Interp's; a flat instruction's agreement is
`Interp.flat_core_normal`/`Interp.flat_core_abrupt`, read back by region completeness on the
call-free fragment.

**`bridge_fwd_closedX`**: the instance with the typed closed extended oracle `closedXOk`, from a
typed native run (`Interp.TypedT`, no host), with no oracle hypothesis.

Not claimed here: the converse (region runs of lowered trees are native runs), which needs flat
completeness (Core runs of flat instructions are `evalFlat` results) and is the next step; the
frame and machine statements built on it.
-/

namespace Silmaril.Wasm.Cfg.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen

variable {H : Type}

/-- **The forward bridge**: typed, checked native runs with a sound oracle are region runs of
the lowered code with the same oracle, ending as `ResOut` says. -/
theorem bridge_fwd {P P₀ : Profile} {host host₀ : HostSemantics H} {C : Abstract.CallRel H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : Abstract.CallXT.EvalOXT C s f stk es r)
    {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : Interp.StoreChkE Interp.tExt s.funcs)
    (hchk : Interp.chkE Interp.tExt s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out) :
    ∃ s' f' o, Region.RunC P host C s f stk.reverse (expression (BExpr.lowerList es)) s' f' o ∧
      ResOut C s' f' o r :=
  Proofs.Bridge.fwd (P := P) (host := host) hC h hS hchk

/-- **The forward bridge for the typed closed extended oracle** (no host, every profile, no
oracle hypothesis): a typed native run with `closedXOk` is a region run of the lowered code with
`closedXOk`, ending as `ResOut` says. -/
theorem bridge_fwd_closedX (P : Profile) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow}
    (h : Abstract.CallX.EvalOX Machine.closedXOk s f stk es r) (ht : Interp.TypedT s f stk es) :
    ∃ s' f' o, Region.RunC P Interp.noHostX Machine.closedXOk s f stk.reverse
      (expression (BExpr.lowerList es)) s' f' o ∧ ResOut Machine.closedXOk s' f' o r := by
  obtain ⟨_, labels, ret, out, hS, hchk, -⟩ := id ht
  exact bridge_fwd (Proofs.Bridge.oracleSoundT_closedXOk P)
    (Interp.OracleX.evalOXT_of_typedT (Proofs.Bridge.oracleSoundT_closedXOk P)
      Proofs.Bridge.keepsTy_closedXOk h ht) hS hchk

end Silmaril.Wasm.Cfg.Bridge
