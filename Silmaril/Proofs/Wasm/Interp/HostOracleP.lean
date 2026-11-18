module

public import Silmaril.Proofs.Wasm.Interp.PendClose
public import Silmaril.Proofs.Wasm.Interp.HostOracle
public import Silmaril.Wasm.Abstract.HostEvalP.Thms

/-!
# The host oracle for the canonical relation is sound (proofs)

`Abstract.HostEvalP.hostCallXP host` answers a Wasm callee by running its body in
`CallXP.EvalOXP` (the frame left by `CallXP.FrameP`, a pending tail call answered by the same
oracle) and a host callee by the host. For hosts in the typed host slice (`HostSliceT`, possibly
throwing) that also keep the exception checker's store check and the tag invariants
(`HostSliceE tags`),
its answers on stores with the tag invariants are sound (`SoundAnsE`, every `call_ref` form), by
least-fixpoint induction as `closedCallXP_sound`:

* a Wasm callee answers soundly by `soundAnsP_of_body`, its calls (and its pending tail call,
  possibly of a host function) answered by the induction hypothesis;
* a host callee answers by one Core step `call_ref-hostfunc` (`soundAnsE_hostAns`); a thrown
  host exception `t` is that step to `throwing t`, the exception's final form at the call site.

Hence `evalOXP_host_good`: runs against the host oracle are Core 3.0 runs with that host.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract (hostAns resFlow)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.HostEvalP

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **What the exception checker needs of the host**, beyond `HostSliceT`: its answers keep
the store check with `ehExt tags` (so functions it appends pass the exception checker) and the
tag invariants `TagsOk tags` (tags unchanged, exceptions well formed). -/
structure HostSliceE (tags : List TagInst) (host : HostSemantics H) : Prop where
  chk : ∀ h s vs s' r, host h s vs (.returned s' r) →
    StoreChkE (ehExt tags) s.funcs → StoreChkE (ehExt tags) s'.funcs
  tags : ∀ h s vs s' r, host h s vs (.returned s' r) → TagsOk tags s → TagsOk tags s'

/-- **A host answer is sound**, in every `call_ref` form: one Core step `call_ref-hostfunc`. -/
theorem soundAnsE_hostAns {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {us : List Val}
    {out : Store H × Binaryen.Flow} (hh : hostAns host s a us out) (hts : TagsOk tags s) :
    SoundAnsE tags P host s a us out := by
  obtain ⟨fi, h, r, hfi, hcode, hhost, hfl⟩ := hh
  refine ⟨hE.tags _ _ _ _ _ hhost hts, ?_⟩
  intro f fi' ps rs c hS hfi' hty hn hcr
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain ⟨ps', rs', he, hpl, hrl⟩ := expand_of_funcType hty
  have hstep : Step P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, r.toAdmin⟩ :=
    Step.callRefHost hcr hfi he (hn.trans hpl.symm) hcode hhost
  have hF := hH.funcs _ _ _ _ _ hhost
  have hG : FuncsGoodE (ehExt tags) s.funcs out.1.funcs :=
    ⟨hF.1, hE.chk _ _ _ _ _ hhost, hF.2.2⟩
  rw [hfl]
  rcases r with ws | t | _
  · have hw := hH.arity s a fi h ps rs us ws out.1 hfi hcode hty hhost
    refine ⟨⟨some rs.length, .inr rfl, by simp [FlowOkE, resFlow, hw], hG⟩, fun vs hvs => ?_,
      fun h' => by simp [resFlow] at h', fun t h' => by simp [resFlow] at h'⟩
    simp only [resFlow, Binaryen.Flow.retVals, Option.some.injEq] at hvs
    subst hvs
    have : (ws.reverse.take rs.length).reverse = ws := by
      rw [List.take_of_length_le (by simp [hw])]
      simp
    rw [this]
    exact .single hstep
  · exact ⟨⟨none, .inl rfl, trivial, hG⟩,
      fun vs hvs => by simp [resFlow, Binaryen.Flow.retVals] at hvs,
      fun h' => by simp [resFlow] at h',
      fun t' h' => by
        simp only [resFlow, Binaryen.Flow.throw.injEq] at h'
        subst h'
        exact .single hstep⟩
  · exact ⟨⟨none, .inl rfl, trivial, hG⟩,
      fun vs hvs => by simp [resFlow, Binaryen.Flow.retVals] at hvs, fun _ => .single hstep,
      fun t h' => by simp [resFlow] at h'⟩

/-- **The host oracle's answers on stores with the tag invariants are sound**, by least-fixpoint
induction. -/
theorem hostCallXP_sound {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) :
    ∀ (s : Store H) a us out, hostCallXP host s a us out → TagsOk tags s →
      SoundAnsE tags P host s a us out := by
  let Q : Abstract.CallRel H := fun s a us out =>
    hostCallXP host s a us out ∧ (TagsOk tags s → SoundAnsE tags P host s a us out)
  have hQ : hostCallXP host ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us out (⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩ | hh)
    · refine ⟨?_, fun hts => ?_⟩
      · rw [hostCallXP_fixpoint]
        exact .inl ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1,
          hfr.mono fun _ _ _ _ h => h.1⟩
      · let C' : Abstract.CallRel H := fun s a us out => TagsOk tags s ∧ Q s a us out
        have hC' : OracleSoundTE (ehExt tags) P host C' true :=
          fun s s₂ f a fi ps rs us fl c hS hfi hty hn hcr hcall =>
            let h := (hcall.2.2 hcall.1).2 f fi ps rs c hS hfi hty hn hcr
            ⟨h.1, h.2.1, h.2.2.1⟩
        have hT' : OracleThrowsE (ehExt tags) P host C' :=
          fun s s₂ f a fi ps rs us t c hS hfi hty hn hcr hcall =>
            ((hcall.2.2 hcall.1).2 f fi ps rs c hS hfi hty hn hcr).2.2.2 t rfl
        have hG' : OracleTagsE tags C' := fun _ _ _ _ _ hcall _ => (hcall.2.2 hcall.1).1
        have hkeep : ∀ s a us out, Q s a us out → TagsOk tags s → TagsOk tags out.1 :=
          fun _ _ _ _ hq ht => (hq.2 ht).1
        obtain ⟨h₁, d'⟩ := TagsOk.restrictP hkeep d hts
        exact soundAnsP_of_body hC' hT' hG' hfi hcode hts d' (FrameP.restrictI hkeep hfr h₁).2
    · refine ⟨?_, fun hts => soundAnsE_hostAns hH hE hh hts⟩
      rw [hostCallXP_fixpoint]
      exact .inr hh
  exact fun s a us out h hg => (hQ _ _ _ _ h).2 hg

/-- **The host oracle on stores with the tag invariants**, as a call oracle. -/
def hostP (tags : List TagInst) (host : HostSemantics H) : Abstract.CallRel H :=
  fun s a us out => TagsOk tags s ∧ hostCallXP host s a us out

theorem oracleSoundTE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleSoundTE (ehExt tags) P host (hostP tags host) true :=
  fun _ _ f _ fi ps rs _ _ c hS hfi hty hn hcr ⟨hg, hcl⟩ =>
    let h := (hostCallXP_sound (P := P) hH hE _ _ _ _ hcl hg).2 f fi ps rs c hS hfi hty hn hcr
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem oracleThrowsE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleThrowsE (ehExt tags) P host (hostP tags host) :=
  fun _ _ f _ fi ps rs _ t c hS hfi hty hn hcr ⟨hg, hcl⟩ =>
    ((hostCallXP_sound (P := P) hH hE _ _ _ _ hcl hg).2 f fi ps rs c hS hfi hty hn hcr).2.2.2 t rfl

theorem oracleTagsE_hostP {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) : OracleTagsE tags (hostP tags host) :=
  fun _ _ _ _ _ ⟨hg, hcl⟩ _ =>
    (hostCallXP_sound (P := Numerics.Profile.spec) hH hE _ _ _ _ hcl hg).1

/-- **Runs against the host oracle are Core 3.0 runs with that host.** -/
theorem evalOXP_host_good {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP (hostCallXP host) s f stk es r) (hg : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      CoreGoodP (ehExt tags) P host s f stk es r := by
  have hkeep : ∀ s a us out, hostCallXP host s a us out → TagsOk tags s → TagsOk tags out.1 :=
    fun _ _ _ _ hcl hg => (hostCallXP_sound (P := P) hH hE _ _ _ _ hcl hg).1
  exact evalOXP_goodP (oracleSoundTE_hostP hH hE) (oracleThrowsE_hostP hH hE)
    (oracleTagsE_hostP hH hE) (TagsOk.restrictP hkeep h hg).2 hg

end Silmaril.Wasm.Interp
