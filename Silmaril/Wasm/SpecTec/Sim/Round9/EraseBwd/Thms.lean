module

public import Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.EraseBwd.StripInj

/-!
# Round 9, REH: the backward SpecTec leaf (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd`; definitions in `Round9/EraseBwd/Defs.lean`,
proofs in `Silmaril/Proofs/Wasm/SpecTec/Sim/Round9/EraseBwd/`.

```lean
theorem eraseBwdAt_param (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (hb : HostExportBlind host) (hp : HostExportParam host) (c : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hbc : BoundedSelE c) (hic : StripInj c) :
    CoreStrip.EraseBwdAt hn (Profile.spec nd r) host c
theorem eraseBwdAt_modsSub … (hm : HostMods.HostModsSub host) … :
    CoreStrip.EraseBwdAt hn (Profile.spec nd r) host c
theorem exactAt_param … (hp : HostExportParam host) … : CoreStrip.ExactAt hn (Profile.spec nd r) host c
theorem leavesBwdAt_stripInj … (hpm : HostExportParam host ∨ HostMods.HostModsSub host) … :
    EraseBwdAt hn (Profile.spec nd r) host c ∧ ExactAt hn (Profile.spec nd r) host c
theorem leavesREHBwd_of_out (h : LeavesREHBwdOut) : BadRules.LeavesREHBwd
theorem leavesREHBwd_iff_out : BadRules.LeavesREHBwd ↔ LeavesREHBwdOut
theorem wholeStepValidREH_of_out (h : LeavesREHBwdOut) : Round7.Task.wholeStepValidREH
```

The backward leaf lifts to the exact successor `configV hn (mapConfig (unstrip c) d₀)` of the
given stripped successor `configV hn d₀`; no Core round trip is involved on the SpecTec side.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.eraseBwdAt_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseBwdAt_param

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.eraseBwdAt_modsSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseBwdAt_modsSub

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.exactAt_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exactAt_param

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.leavesBwdAt_stripInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms leavesBwdAt_stripInj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.leavesREHBwd_iff_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms leavesREHBwd_iff_out

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.wholeStepValidREH_of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREH_of_out

end Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd
