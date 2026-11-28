module

public import Silmaril.Wasm.Institution.Operational.HostCall.V1.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.V1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.V1

open Execution.Runtime (Frame FuncAddr Value)
open Wasm.V1.Execution

/-- Native direct resolution leaves the entire stack and continuation in place. -/
theorem direct_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {index : FuncIdx} {address : FuncAddr} {stack : List Value} {tail : List Admin} {dst : Config H}
    (resolved : caller.module.funcs[index.toNat]? = some address) :
    Step host ⟨s, caller, values stack ++ .source (.call index) :: tail⟩ dst ↔
      dst = ⟨s, caller, values stack ++ .invoke address :: tail⟩ :=
  Proofs.direct_step_iff resolved

/-- Direct resolution preserves all operands and the active caller. -/
theorem source_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H}
    {caller : Frame} {saved args : List Value} {tail : List Admin} {dst : Config H}
    (resolved : caller.module.funcs[site.index.toNat]? = some site.address) :
    Step host (site.source s caller saved args tail) dst ↔ dst = site.pending s caller saved args tail :=
  Proofs.source_step_iff resolved

/-- The exact caller prefix, argument suffix, and continuation form a native callout. -/
theorem Site.Checked.callout_at {H : Type} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} (checked : site.Checked s caller args) :
    CalloutAt (site.pending s caller saved args tail) (site.callout saved args tail) :=
  Proofs.callout_at checked

/-- The exact saturated suffix is submitted to the host. A returning outcome
supplies the entire next store and result. Declared divergence is a self-step. -/
theorem pending_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} {dst : Config H} (checked : site.Checked s caller args) :
    Step host (site.pending s caller saved args tail) dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧ dst = resumed s' caller saved tail r) ∨
      (host site.target s args .diverged ∧ dst = site.pending s caller saved args tail) :=
  Proofs.pending_step_iff checked

/-- With the embedding's proof of its contract, native resumption supplies
the declared payload and an output store related to the input store. -/
theorem checked_pending_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} {dst : Config H} {preserves : Store H → Store H → Prop}
    (checked : site.Checked s caller args) (contract : site.ReturnContract host preserves s args) :
    Step host (site.pending s caller saved args tail) dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧ ResultTyped site.signature.results r ∧
        preserves s s' ∧ dst = resumed s' caller saved tail r) ∨
      (host site.target s args .diverged ∧ dst = site.pending s caller saved args tail) :=
  Proofs.checked_pending_step_iff checked contract

/-- Every finite prefix stops at source, at the pending call (including after
divergence self-steps), or has a checked return or trap followed by a native
caller run. The contract concerns delivery of this call's outcome. -/
theorem run_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H}
    {caller : Frame} {saved args : List Value} {tail : List Admin} {dst : Config H}
    {preserves : Store H → Store H → Prop} (checked : site.Checked s caller args)
    (contract : site.ReturnContract host preserves s args) :
    Steps host (site.source s caller saved args tail) dst ↔
      dst = site.source s caller saved args tail ∨ dst = site.pending s caller saved args tail ∨
      ∃ s' r, host site.target s args (.returned s' r) ∧ ResultTyped site.signature.results r ∧
        preserves s s' ∧ Steps host (resumed s' caller saved tail r) dst :=
  Proofs.run_iff checked contract

end Silmaril.Wasm.Institution.Operational.HostCall.V1
