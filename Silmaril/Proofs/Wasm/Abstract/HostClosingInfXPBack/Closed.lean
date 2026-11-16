module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Progress

/-!
# Host-free Core divergence is closed canonical divergence (proofs)

In the deterministic profile `SingleThreaded.profile o`, with host functions allowed in the store:

* `not_hreach_of_diverges`: a checked problem whose Core run diverges host-free reaches no host
  call in the closed semantics: by `hreach_core_both` a reach is a Core run to a configuration at a
  host call, which has no host-free step, and a divergent run of a typed configuration passes
  through every host-free run (`diverges_through_steps`);
* `no_outcome_of_diverges`: it has no closed outcome: by `evalOXP_closed_good` an outcome is a Core
  run to a final form, which has no step (`outcome_ends_stuck`);
* `evalDivXP_of_diverges`: so a typed problem whose Core run diverges host-free diverges in the
  closed canonical semantics (`evalDivXP_of_noReach`);
* `funDivXP_of_invoke_diverges`: a typed invocation diverging host-free in Core is `FunDivXP` (the
  converse of `Interp.PProgress.invoke_diverges_of_funDivXP`), without `Interp.WasmFuncsT`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Binaryen (BExpr liftInstrs truthy)

variable {H : Type} {o : GrowOracle} {tags : List TagInst}

/-- The host with no outcome. -/
abbrev NH : HostSemantics H := fun _ _ _ _ => False

/-- A divergent run of a typed configuration does not reach a configuration at a host call
host-free. -/
theorem not_diverges_at_host {K T : Config H} (ht : Sim.ContextTyped K)
    (hK : Diverges (profile o) NH K) (hT : Steps (profile o) NH K T)
    (hdec : (decompose? T.store T.code).isSome) : False := by
  have hD := Silmaril.Wasm.Abstract.diverges_through_steps (o := o) hT ht hK
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdec
  obtain ⟨c', hst, -⟩ := hD.unfold
  exact Silmaril.Wasm.Abstract.noFree_of_decompose hx hst

/-- A divergent run of a typed configuration does not reach a final form host-free. -/
theorem not_diverges_at_end {K : Config H} {s' : Store H} {f' : Frame} {c' : List Admin}
    {oc : Outcome} (ht : Sim.ContextTyped K) (hK : Diverges (profile o) NH K)
    (hT : Steps (profile o) NH K ⟨s', f', c'⟩) (he : oc.Ends c') : False := by
  have hD := Silmaril.Wasm.Abstract.diverges_through_steps (o := o) hT ht hK
  obtain ⟨c'', hst, -⟩ := hD.unfold
  exact Silmaril.Wasm.Abstract.outcome_ends_stuck he s' f' c'' hst

theorem typedP_ctx' {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (ht : TypedP tags s f stk es) : Sim.ContextTyped ⟨s, f, xcode stk es⟩ := by
  obtain ⟨rest, -, -, -, -, -, hct, -, -⟩ := ht
  exact Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc] using hct)

variable {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}

/-- **A problem diverging host-free in Core reaches no host call.** -/
theorem not_hreach_of_diverges (ht : TypedP tags s f stk es)
    (hd : Diverges (profile o) NH ⟨s, f, xcode stk es⟩) : ¬ HReach s f stk es := fun h => by
  obtain ⟨T, hT, hdec⟩ := (hreach_core_both (P := profile o) (host := NH)).1 _ _ _ _ h
    ht.checked .hole
  exact not_diverges_at_host (typedP_ctx' ht) hd hT hdec

/-- **A problem diverging host-free in Core has no closed outcome.** -/
theorem no_outcome_of_diverges (ht : TypedP tags s f stk es)
    (hd : Diverges (profile o) NH ⟨s, f, xcode stk es⟩) :
    ¬ ∃ r, EvalOXP closedCallXP s f stk es r := by
  rintro ⟨r, d⟩
  have hct := typedP_ctx' ht
  obtain ⟨-, labels, ret, out, hS, hc, -, -, hts⟩ := ht
  obtain ⟨-, -, hG⟩ := evalOXP_closed_good (P := profile o) (host := NH) d hts
  obtain ⟨s', f', c', oc, hrun, he, -⟩ := hG hS hc
  exact not_diverges_at_end hct hd hrun he

/-- **Host-free Core divergence of a typed problem is closed canonical divergence.** -/
theorem evalDivXP_of_diverges (ht : TypedP tags s f stk es)
    (hd : Diverges (profile o) NH ⟨s, f, xcode stk es⟩) : EvalDivXP s f stk es :=
  evalDivXP_of_noReach ht (not_hreach_of_diverges ht hd) (no_outcome_of_diverges ht hd)

/-- **Host-free Core divergence of a typed invocation is `FunDivXP`**, on a store that may hold
host functions. -/
theorem funDivXP_of_invoke_diverges {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hd : Diverges (profile o) NH (invoke s a vs)) : FunDivXP s a vs := by
  have hct := invoke_callTyped hs hok hS hts
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hn⟩, -⟩ := id hct
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  have hctx := Sim.ContextTyped.of_configOk hcfg
  have hinv : invoke s a vs = ⟨s, {}, Interp.callCode [] vs a (.callRefType fi.type) []⟩ := by
    rw [invoke_eqP hfi]; simp [Interp.callCode, vals]
  refine funDivXP_of_noReach hct (fun h => ?_) (fun ⟨⟨s₂, fl⟩, hcall⟩ => ?_)
  · obtain ⟨T, hT, hdec⟩ := (hreach_core_both (P := profile o) (host := NH)).2 _ _ _ h hct.1
      .hole {} [] (.callRefType fi.type) [] trivial
    rw [← hinv] at hT
    exact not_diverges_at_host hctx hd hT hdec
  · obtain ⟨hret, htr, hth⟩ := invoke_answer_steps (P := profile o) (host := NH) hS hts hfi hty
      hn hcall
    rcases calleeP_flow hct.1 hcall with ⟨ws, hws⟩ | hab
    · exact not_diverges_at_end (oc := .normal _) hctx hd (hret ws hws) rfl
    · cases fl with
      | trap => exact not_diverges_at_end (oc := .trap) hctx hd (htr rfl) rfl
      | throw t => exact not_diverges_at_end (oc := .throw t) hctx hd (hth t rfl) rfl
      | _ => exact hab.elim

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
