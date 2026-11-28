module

public import Silmaril.Wasm.Institution.Operational.HostCall.V1.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.V1.Proofs

open Execution.Runtime (Callout Frame FuncAddr Value)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Computed (lime_direct_call_iff)

theorem direct_step_iff {H : Type} {host : HostSemantics H} {index : FuncIdx} {address : FuncAddr} {s : Store H}
    {caller : Frame} {stack : List Value} {tail : List Admin} {dst : Config H}
    (resolved : caller.module.funcs[index.toNat]? = some address) :
    Step host (⟨s, caller, values stack ++ .source (.call index) :: tail⟩ : Config H) dst ↔ dst = ⟨s, caller, values stack ++ .invoke address :: tail⟩ := by
  constructor
  · intro move
    have noCallout (c : Callout H Wasm.V1.Instr) : ¬ CalloutAt (⟨s, caller, values stack ++ .source (.call index) :: tail⟩ : Config H) c := by
      intro located
      obtain ⟨d, computed, _⟩ := decompose?_complete located
      simp [decompose?, asValue?] at computed
    have internal := (Step.internal_iff_of_not_callout noCallout).mp move
    have mapped := internal.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ impossible => impossible)
    have decoded := (lime_direct_call_iff (stack := stack) (tail := codeToLime tail) resolved).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        Execution.Runtime.AdminInstr.map, Wasm.V1.Instr.toLime] using mapped)
    apply CallContinuation.config_toLime_injective H
    simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
      Execution.Runtime.AdminInstr.map] using decoded
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.call (host := host) s caller index address resolved) stack tail

theorem source_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H}
    {caller : Frame} {saved args : List Value} {tail : List Admin} {dst : Config H}
    (resolved : caller.module.funcs[site.index.toNat]? = some site.address) :
    Step host (site.source s caller saved args tail) dst ↔ dst = site.pending s caller saved args tail :=
  direct_step_iff resolved

theorem callout_at {H : Type} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} (checked : site.Checked s caller args) :
    CalloutAt (site.pending s caller saved args tail) (site.callout saved args tail) := by
  have count : args.length = site.signature.params.length := by
    simpa using congrArg List.length checked.arguments
  refine ⟨?_, checked.allocated, count⟩
  simp [Site.pending, Site.callout, Callout.fill, Callout.redex, Execution.Runtime.EvalCtx.plug,
    coding, values, List.map_append, List.append_assoc]

theorem pending_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} {dst : Config H} (checked : site.Checked s caller args) :
    Step host (site.pending s caller saved args tail) dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧ dst = resumed s' caller saved tail r) ∨
      (host site.target s args .diverged ∧ dst = site.pending s caller saved args tail) := by
  exact (CalloutAt.step_iff (callout_at checked)).trans Answer.iff

theorem checked_pending_step_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H} {caller : Frame}
    {saved args : List Value} {tail : List Admin} {dst : Config H} {preserves : Store H → Store H → Prop}
    (checked : site.Checked s caller args) (contract : site.ReturnContract host preserves s args) :
    Step host (site.pending s caller saved args tail) dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧ ResultTyped site.signature.results r ∧
        preserves s s' ∧ dst = resumed s' caller saved tail r) ∨
      (host site.target s args .diverged ∧ dst = site.pending s caller saved args tail) := by
  rw [pending_step_iff checked]
  constructor
  · rintro (⟨s', r, behavior, eq⟩ | diverged)
    · exact .inl ⟨s', r, behavior, (contract _ _ behavior).1, (contract _ _ behavior).2, eq⟩
    · exact .inr diverged
  · rintro (⟨s', r, behavior, _, _, eq⟩ | diverged)
    · exact .inl ⟨s', r, behavior, eq⟩
    · exact .inr diverged

private theorem pending_run {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H}
    {caller : Frame} {saved args : List Value} {tail : List Admin} {src dst : Config H}
    {preserves : Store H → Store H → Prop} (checked : site.Checked s caller args)
    (contract : site.ReturnContract host preserves s args) (run : Steps host src dst)
    (pending : src = site.pending s caller saved args tail) :
    dst = site.pending s caller saved args tail ∨
      ∃ s' r, host site.target s args (.returned s' r) ∧ ResultTyped site.signature.results r ∧
        preserves s s' ∧ Steps host (resumed s' caller saved tail r) dst := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl pending
  | head step rest ih =>
    rw [pending] at step
    rcases (checked_pending_step_iff checked contract).mp step with
      ⟨s', r, behavior, typed, stored, eq⟩ | ⟨_, again⟩
    · exact .inr ⟨s', r, behavior, typed, stored, eq ▸ rest⟩
    · exact ih again

theorem run_iff {H : Type} {host : HostSemantics H} {site : Site H} {s : Store H}
    {caller : Frame} {saved args : List Value} {tail : List Admin} {dst : Config H}
    {preserves : Store H → Store H → Prop} (checked : site.Checked s caller args)
    (contract : site.ReturnContract host preserves s args) :
    Steps host (site.source s caller saved args tail) dst ↔
      dst = site.source s caller saved args tail ∨ dst = site.pending s caller saved args tail ∨
      ∃ s' r, host site.target s args (.returned s' r) ∧ ResultTyped site.signature.results r ∧
        preserves s s' ∧ Steps host (resumed s' caller saved tail r) dst := by
  constructor
  · intro run
    rcases run.cases_head with same | ⟨next, step, rest⟩
    · exact .inl same.symm
    · exact .inr (pending_run checked contract rest ((source_step_iff checked.resolved).mp step))
  · rintro (rfl | rfl | ⟨s', r, behavior, typed, store, rest⟩)
    · exact .refl
    · exact .single ((source_step_iff checked.resolved).mpr rfl)
    · have answer := (checked_pending_step_iff (saved := saved) (tail := tail) (dst := resumed s' caller saved tail r)
        checked contract).mpr
        (.inl ⟨s', r, behavior, typed, store, rfl⟩)
      exact .head ((source_step_iff checked.resolved).mpr rfl) (.head answer rest)

end Silmaril.Wasm.Institution.Operational.HostCall.V1.Proofs
