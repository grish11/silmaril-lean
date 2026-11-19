module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Defs

/-!
# Round 9, REH: the backward SpecTec leaf (definitions)

`Round9.BadRules.LeavesREHBwd` is what is left of `Round7.Task.wholeStepValidREH`: at every
`ConfigOk`, `BoundedSelE` configuration `c` and every finite, `HostOk`, export-blind host, the
backward erasure leaf `CoreStrip.EraseBwdAt` and the export leaf `CoreStrip.ExactAt`.

**Where the leaves are proved.** On `StripInj c` (no two module instances of `c` differ only in
their export lists), for a host that is also export-parametric (`HostExportParam`) or invents no
module (`HostMods.HostModsSub`): round 7's export swap (`Round7.EraseDer.swapEquiv_holds`,
`Round7.HostMods.swapAt_fwdM`) lifts a stripped step to `configV hn c`, at the exact successor
`configV hn (mapConfig (unstrip c) d₀)` whose erasure is the given one
(`Round9.EraseBwd.leavesBwdAt_stripInj`). This is the domain where `Round7.Task.wholeStepValidREI`
and `Round7.HostMods.StepValidREM` already hold; it adds nothing to what is known of REH there.

**What is left** (`LeavesREHBwdOut`): the same two leaves at the configurations and hosts outside
that domain. In particular every configuration with two module instances that differ only in
their export lists (`Round7.REGap.collideCfg`) is still open. There the stripped successor does
not determine the export lists of the original one, and the leaf needs a derivation-level lift:
see `Round9.ElseLift` for the `otherwise` part of it.

`LeavesREHBwdOut` is `LeavesREHBwd` restricted to the complement of a proved case
(`Round9.EraseBwd.leavesREHBwd_of_out`, and the converse); it is bookkeeping, not a proof of
`LeavesREHBwd`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7 (BoundedSelE StripInj HostExportParam)

/-- **`BadRules.LeavesREHBwd` outside the proved case**: the backward and export leaves at
configurations and hosts where `StripInj c` fails, or the host is neither export-parametric nor
module-preserving. Equivalent to `LeavesREHBwd` (`Round9.EraseBwd.leavesREHBwd_iff_out`). -/
def LeavesREHBwdOut : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → Round7.HostExportBlind host →
      ∀ (nd : Bool) (r : RelaxedChoice) (c : Config H) (ts : List CValType),
        ConfigOk c ts → BoundedSelE c →
        ¬ (StripInj c ∧ (HostExportParam host ∨ Round7.HostMods.HostModsSub host)) →
        CoreStrip.EraseBwdAt hn (Profile.spec nd r) host c ∧
          CoreStrip.ExactAt hn (Profile.spec nd r) host c

end Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd
