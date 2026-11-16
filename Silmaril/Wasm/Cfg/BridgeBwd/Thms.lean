module

public import Silmaril.Wasm.Cfg.Bridge.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
import Silmaril.Proofs.Wasm.Cfg.BridgeBwd

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

Not claimed here: the tree-level converse (region runs of lowered typed trees are native
`EvalOX` runs, `ResOut`), which composes this case with the structured and call cases.
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

end Silmaril.Wasm.Cfg.Bridge
