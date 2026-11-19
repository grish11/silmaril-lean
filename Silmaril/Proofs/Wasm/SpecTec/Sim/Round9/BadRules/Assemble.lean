module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.HostRules
public import Silmaril.Wasm.SpecTec.Sim.Round9.REFwd.Thms

/-!
# Round 9, RE: `BadFwdN` at export-blind hosts, and the forward leaf of REH

`badFwdN_BI`: the seven rules of `BadN.BadFwdN` go to the erased side at round 4's primitives, for
an injective naming and a finite, export-blind host (`ruleFwd_host`, `ruleFwd_grow`,
`ruleFwd_block`). With round 9's `REFwd.eraseFwdAt_of_blindN` this is the forward leaf
`CoreStrip.EraseFwdAt` at every configuration (`eraseFwdAt_blind`), so `CoreStrip.LeavesREH`, and
with it `Round7.Task.wholeStepValidREH`, follow from the two other leaves (`LeavesREHBwd`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7

variable {H : Type}

/-- **The seven rules of `BadFwdN` at round 4's primitives**, for an injective naming and a
finite, export-blind host. -/
theorem badFwdN_BI (P : Silmaril.Wasm.Numerics.Profile) {hn : H → String}
    {host : HostSemantics H} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hb : HostExportBlind host) : BadN.BadFwdN (NxPrims.envBI P hn host) := by
  refine badFwdN_of_rules fun nm hnm => ?_
  simp only [badNames, List.mem_cons, List.not_mem_nil, or_false] at hnm
  rcases hnm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ruleFwd_host P hn host hinj hf hb (by decide)
  · exact ruleFwd_host P hn host hinj hf hb (by decide)
  · exact ruleFwd_grow P hn host (by decide)
  · exact ruleFwd_grow P hn host (by decide)
  · exact ruleFwd_block P hn host (by decide)
  · exact ruleFwd_block P hn host (by decide)
  · exact ruleFwd_block P hn host (by decide)

/-- **The forward leaf of RE at every configuration**, for an injective naming and a finite,
export-blind host. -/
theorem eraseFwdAt_blind (P : Silmaril.Wasm.Numerics.Profile) {hn : H → String}
    {host : HostSemantics H} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hb : HostExportBlind host) (c : Config H) : CoreStrip.EraseFwdAt hn P host c :=
  REFwd.eraseFwdAt_of_blindN hb P (badFwdN_BI P hinj hf hb) c

/-- **`LeavesREH` from its two remaining leaves.** -/
theorem leavesREH_of_bwd (h : LeavesREHBwd) : CoreStrip.LeavesREH :=
  fun H hn hinj host hf hh hb nd r c ts hc hbc =>
    ⟨eraseFwdAt_blind _ hinj hf hb c, (h H hn hinj host hf hh hb nd r c ts hc hbc).1,
      (h H hn hinj host hf hh hb nd r c ts hc hbc).2⟩

/-- **`Round7.Task.wholeStepValidREH` from the backward and export leaves.** -/
theorem wholeStepValidREH_of_bwd (h : LeavesREHBwd) : Task.wholeStepValidREH :=
  CoreStrip.wholeStepValidREH_of_leaves (leavesREH_of_bwd h)

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
