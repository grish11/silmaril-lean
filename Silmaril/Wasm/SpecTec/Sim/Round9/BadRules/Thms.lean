module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.Assemble

/-!
# Round 9, RE: the seven rules of `BadFwdN`, and the forward leaf of REH (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.BadRules`; see `docs/projects/wasm-spec-bridge.md`.
Definitions are in `Round9/BadRules/Defs.lean`, proofs in `Silmaril/Proofs/…/Round9/BadRules/`.

* **`badFwdN_of_rules`**: `BadN.BadFwdN (utf8Env B)` from `RuleFwdNm` at the seven names
  (kernel check `badNames_fixed`).
* **`ruleFwd_block`** (`block`, `loop`, `try_table`): `$blocktype_` commutes with erasure of the
  state (`applies_blocktype_erase`), the rest of the premise and the conclusion pass the checks
  (kernel check `btShape_fixed`).
* **`ruleFwd_grow`** (`table.grow-succeed`, `memory.grow-succeed`): the updater's body is evaluated
  across erasure by hand (`withInstBody_erase`, `callW_erase`; kernel check `growShapeN_fixed`).
* **`ruleFwd_host`** (`call_ref-hostfunc-res`, `call_ref-hostfunc-div`): the `$hostcall` premise
  goes across for an injective naming and a finite, export-blind host (`hostPrem_fwd`; kernel
  check `hostShapeN_fixed`).
* **`badFwdN_BI`**: `BadN.BadFwdN (NxPrims.envBI P hn host)` for an injective naming and a
  finite, export-blind host.
* **`eraseFwdAt_blind`**: the forward leaf `CoreStrip.EraseFwdAt` at every configuration, for such
  hosts. **`leavesREH_of_bwd`**, **`wholeStepValidREH_of_bwd`**: `CoreStrip.LeavesREH` and
  `Round7.Task.wholeStepValidREH` from `LeavesREHBwd` (the backward and export leaves only).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.badFwdN_of_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms badFwdN_of_rules

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.ruleFwd_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_block

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.ruleFwd_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_grow

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.ruleFwd_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleFwd_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.badFwdN_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms badFwdN_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.eraseFwdAt_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseFwdAt_blind

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.leavesREH_of_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms leavesREH_of_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.wholeStepValidREH_of_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidREH_of_bwd

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
