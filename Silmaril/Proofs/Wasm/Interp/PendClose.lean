module

public import Silmaril.Proofs.Wasm.Interp.PendSim
public import Silmaril.Proofs.Wasm.Interp.EHClose
public import Silmaril.Wasm.Abstract.XRecursionP.Thms

/-!
# The closure with pending tail calls is a sound oracle (F5, proofs)

`closedP tags` answers calls by the closure `XRecursionP.closedCallXP` — callee bodies run in
`CallXP.EvalOXP`, every call form allowed, and a pending tail call is made only when the callee's
frame is left (`CallXP.FrameP`) — on stores satisfying the tag invariants (`TagsOk tags`).

* `soundAnsP_of_body`: a callee body with a sound run, its frame left by `FrameP`, answers soundly
  (`SoundAnsE`, every `call_ref` form): a flow leaves the label and frame as in `EHClose`, a trap
  that is Core's pending null tail call by `return_call_ref-frame-null`, and a pending tail call
  by `return_call_ref-label` and `return_call_ref-frame-addr`, after which the tail callee runs
  in the caller's frame and its answer is the oracle's.
* By least-fixpoint induction, `closedP tags` is sound (`oracleSoundTE_closedP`), its thrown
  exceptions are Core throws (`oracleThrowsE_closedP`) and it keeps the tag invariants
  (`oracleTagsE_closedP`); hence `evalOXP_closed_good`: closed runs are Core 3.0 runs, no oracle
  assumed.

The only store invariant is `TagsOk tags`: unlike `EHClose`, callee bodies may contain every call
form (no `StoreXFree`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Restricting the oracle to an invariant of the run -/

/-- **Restriction to a run invariant** for `EvalOXP`: if `I` is kept by flat instructions, by
`throw` and by the oracle's answers, a run from a store satisfying `I` ends in one, and is a run
against the oracle restricted to stores satisfying `I`. -/
theorem EvalOXP.restrictI {C : Abstract.CallRel H} {I : Store H → Prop}
    (hF : ∀ {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Binaryen.Flow},
      Binaryen.evalFlat s f stk i = some (s', f', fl) → I s → I s')
    (hthrow : ∀ {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
      {ts : Validation.Ty (.list .val)} {vs : List Val}, s.tag? f x = some (ta, ti) →
      Validation.Expand ti.type (.func ts .nil) → vs.length = ts.length → I s →
      I (s.addExn ⟨ta, vs⟩))
    (hC : ∀ s a us out, C s a us out → I s → I out.1)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    I s → I r.1 ∧ EvalOXP (fun s a us out => I s ∧ C s a us out) s f stk es r := by
  induction h with
  | nil => exact fun hI => ⟨hI, .nil⟩
  | argsAbort _ ho ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .argsAbort d1 ho⟩
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callOk d1 hfi hty ⟨h1, hcall⟩ hvs d2⟩
  | callTrap _ hfi hty hcall ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callTrap d1 hfi hty ⟨h1, hcall⟩⟩
  | callThrow _ hfi hty hcall ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callThrow d1 hfi hty ⟨h1, hcall⟩⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hF hflat h1)
    exact ⟨h2, .opOk hi d1 hflat d2⟩
  | opStop hi _ hflat hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hF hflat h1, .opStop hi d1 hflat hfl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .blockOk har d1 hvs d2⟩
  | blockBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .blockBrk har d1⟩
  | blockEsc har _ ho ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .blockEsc har d1 ho⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .loopOk har d1 d2⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .loopBack har d1 d2⟩
  | loopBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .loopBrk har d1⟩
  | loopEsc har _ ho ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .loopEsc har d1 ho⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1; obtain ⟨h3, d3⟩ := ih₃ h2
    exact ⟨h3, .ifOk d1 hb har d2 hvs d3⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .ifBrk d1 hb har d2⟩
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .ifEsc d1 hb har d2 ho⟩
  | ifAbort _ ho ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .ifAbort d1 ho⟩
  | callIndOk _ hres hfi hty hy hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callIndOk d1 hres hfi hty hy ⟨h1, hcall⟩ hvs d2⟩
  | callIndRes _ hres ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .callIndRes d1 hres⟩
  | callIndStop _ hres hfi hty hy hcall hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callIndStop d1 hres hfi hty hy ⟨h1, hcall⟩ hfl⟩
  | callRefOk _ hfi hty hy hcall hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI
    obtain ⟨h2, d2⟩ := ih₂ (hC _ _ _ _ hcall h1)
    exact ⟨h2, .callRefOk d1 hfi hty hy ⟨h1, hcall⟩ hvs d2⟩
  | callRefNull _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .callRefNull d1⟩
  | callRefStop _ hfi hty hy hcall hfl ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hC _ _ _ _ hcall h1, .callRefStop d1 hfi hty hy ⟨h1, hcall⟩ hfl⟩
  | tail _ hres hfi hty hy ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tail d1 hres hfi hty hy⟩
  | tailRes _ hres ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tailRes d1 hres⟩
  | throw _ ht he hn ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI
    exact ⟨hthrow ht he (by simp only [List.length_reverse, List.length_take]; omega) h1,
      .throw d1 ht he hn⟩
  | throwRefNull _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .throwRefNull d1⟩
  | throwRefExn _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .throwRefExn d1⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro hI; obtain ⟨h1, d1⟩ := ih₁ hI; obtain ⟨h2, d2⟩ := ih₂ h1
    exact ⟨h2, .tryOk har d1 hvs d2⟩
  | tryBrk har _ ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryBrk har d1⟩
  | tryEsc har _ ho hnt ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryEsc har d1 ho hnt⟩
  | tryCatch har _ hc ih => intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryCatch har d1 hc⟩
  | tryRethrow har _ hc ih =>
    intro hI; obtain ⟨h1, d1⟩ := ih hI; exact ⟨h1, .tryRethrow har d1 hc⟩

/-- Restriction to a run invariant, for leaving the frame. -/
theorem FrameP.restrictI {C : Abstract.CallRel H} {I : Store H → Prop}
    (hC : ∀ s a us out, C s a us out → I s → I out.1) {x : Store H × POut}
    {y : Store H × Binaryen.Flow} (h : FrameP C x y) (hI : I x.1) :
    I y.1 ∧ FrameP (fun s a us out => I s ∧ C s a us out) x y := by
  cases h with
  | flow => exact ⟨hI, .flow⟩
  | tail hcall hfl =>
    have h₂ := hC _ _ _ _ hcall hI
    exact ⟨h₂, .tail ⟨hI, hcall⟩ hfl⟩

/-! ## Leaving the frame -/

section Frame

set_option linter.unusedSectionVars false

variable {n : Nat} {fl : Binaryen.Flow} {ws : List Val} {t : Nat}

theorem tailFlow_retVals_inv (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt)
    (h : (tailFlow n fl).retVals = some ws) : ∃ vs, fl.retVals = some vs ∧ ws = vs.take n := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | _ <;>
    simp_all [tailFlow, Binaryen.Flow.retVals, Binaryen.Flow.Abrupt]

theorem tailFlow_trap_inv (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt)
    (h : tailFlow n fl = .trap) : fl = .trap := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | _ <;>
    simp_all [tailFlow, Binaryen.Flow.retVals, Binaryen.Flow.Abrupt]

theorem tailFlow_throw_inv (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt)
    (h : tailFlow n fl = .throw t) : fl = .throw t := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | _ <;>
    simp_all [tailFlow, Binaryen.Flow.retVals, Binaryen.Flow.Abrupt]

/-- The check of a `tailFlow` result, from the tail callee's. -/
theorem flowOkE_tailFlow {ob ob' : Option Nat} {m : Nat} (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt)
    (hok : FlowOkE true [n] n ob fl) (hob : ob = none ∨ ob = some n) :
    FlowOkE true [m] n ob' (tailFlow n fl) := by
  rcases hfl with ⟨vs, hvs⟩ | hab
  · rw [tailFlow_of_retValsT hvs]
    have := retVals_length hok hob hvs
    show n ≤ (vs.take n).length
    simp only [List.length_take]; omega
  · cases fl with
    | trap => trivial
    | throw => trivial
    | _ => exact absurd hab id

end Frame

/-- **A callee whose body has a sound run, its frame left by `FrameP`, answers soundly.** A flow
leaves the callee's label and frame as in `EHClose.soundAnsE_of_body`; a trap that is Core's
pending null tail call leaves by `return_call_ref-frame-null`; a pending tail call leaves by
`return_call_ref-label` and `return_call_ref-frame-addr`, the tail callee then running in the
caller's frame as the oracle answers it. -/
theorem soundAnsP_of_body {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundTE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s s₁ : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {f₂ : Frame} {o : POut} {out : Store H × Binaryen.Flow}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) (hts : TagsOk tags s)
    (d : EvalOXP C s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s₁, f₂, o))
    (hfr : FrameP C (s₁, o) out) :
    SoundAnsE tags P host s a us out := by
  obtain ⟨ht₁, hA, hCore⟩ := evalOXP_goodP (P := P) (host := host) hC hT hG d hts
  have htout : TagsOk tags out.1 := by
    cases hfr with
    | flow => exact ht₁
    | tail hcall _ => exact hG _ _ _ _ _ hcall ht₁
  refine ⟨htout, ?_⟩
  intro f fi' ps rs c hS hfi' hty hn hcr
  rw [hfi] at hfi'; cases hfi'
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, hob⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length = ps.length + fn.locals.length :=
    forCall_length _ _ hn
  have hb' : chkE (ehExt tags) s.funcs (Frame.forCall fi.module us fn.locals).module
      (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlen]; exact hb
  obtain ⟨hok, hinv, hw⟩ := hA hS hb'
  have hwb := hCore hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := by rw [hn, ← hpl]
  have hrl' : rs'.length = rs.length := by rw [← hrl]
  have enter : Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module us fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    rw [← hrl']
    exact .single (Step.callRefFunc hcr hfi hex hn' hcode)
  cases hfr with
  | @flow _ fl =>
    replace hok : FlowOkE true [rs.length] rs.length ob fl := hok
    refine ⟨⟨ob, hob, hok, hinv.1⟩, fun vs hvs => ?_, fun htr => ?_, fun t hth => ?_⟩
    · have hfl : fl ≠ .trap := by rintro rfl; cases hvs
      obtain ⟨c', o', hrun, he, hm⟩ := run_of_wp (wp_of_wpP hfl hwb)
      have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
        (Steps.label rs.length [] (by simpa [vals] using hrun))
      have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
      have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
        rintro ws rfl
        exact length_of_ends hok hob
      obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
        (funcPost_of_match (s₂ := s₁) (F := f₂) hm hvs hrs hnorm)
      obtain ⟨rfl, rfl⟩ := hK
      exact enter.trans (inner.trans hret)
    · dsimp only at htr
      subst htr
      rcases run_of_wpP_flow hwb with ⟨c', o', hrun, he, hm⟩ | ⟨-, vs, c', rest, hrun, hc⟩
      · have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
          (Steps.label rs.length [] (by simpa [vals] using hrun))
        have hc : c' = [.trap] := by
          rcases o' with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
          exact he
        subst hc
        have out : Steps P host ⟨s₁, f, [.frame rs.length f₂ [.label rs.length [] [.trap]]]⟩
            ⟨s₁, f, [.trap]⟩ :=
          (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
        exact enter.trans (inner.trans out)
      · have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
          (Steps.label rs.length [] (show Steps P host
            ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩
            ⟨s₁, f₂, vals vs ++ .ref .null :: c' :: rest⟩ from by simpa [vals] using hrun))
        exact enter.trans (inner.trans (frame_tailNull (P := P) (host := host) (s := s₁) (f := f)
          (n := rs.length) (F := f₂) (vs := vs) (rest := rest) hc))
    · dsimp only at hth
      subst hth
      obtain ⟨c', o', hrun, he, hm⟩ := run_of_wp (wp_of_wpP (fun h => by cases h) hwb)
      have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
        (Steps.label rs.length [] (by simpa [vals] using hrun))
      have hc : c' = throwing t := by
        rcases o' with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hm
        subst hm
        exact he
      subst hc
      have out : Steps P host ⟨s₁, f, [.frame rs.length f₂ [.label rs.length [] (throwing t)]]⟩
          ⟨s₁, f, throwing t⟩ :=
        (Relation.ReflTransGen.single (Step.ctxtFrame Step.throwRefLabel)).tail Step.throwRefFrame
      exact enter.trans (inner.trans out)
  | @tail _ s₂ a' n args fl hcall hfl =>
    obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, hrs₂⟩ := hw a' args n rfl
    have hnr : n = rs.length := hok
    obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
    have hargs' : args.length = ps₂'.length := by rw [hargs, ← hpl₂]
    have hS₁ : StoreChkE (ehExt tags) s₁.funcs := hinv.1.2.1 hS
    obtain ⟨vs₁, c', rest, hrun, hc'⟩ := run_of_wpP_tail hwb
    have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
      (Steps.label rs.length [] (show Steps P host
        ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩
        ⟨s₁, f₂, vals (vs₁ ++ args) ++ .ref (.func a') :: c' :: rest⟩ from
          by simpa [vals] using hrun))
    have exit := frame_tail_exit (P := P) (host := host) (s := s₁) (f := f) (k := rs.length)
      (F := f₂) (vs₁ := vs₁) (rest := rest) hc' hfi₂ hex₂ hargs'
    have hcr' := isCallRef_retToCallIn hc' f₂.module
    obtain ⟨⟨ob₂, hob₂, hok₂, hfuncs₂⟩, hret₂, htr₂⟩ :=
      hC s₁ s₂ f a' fi₂ ps₂ rs₂ args fl _ hS₁ hfi₂ hty₂ hargs hcr' hcall
    have pre := enter.trans (inner.trans exit)
    rw [hrs₂] at hob₂ hok₂ hret₂
    refine ⟨⟨none, .inl rfl, ?_, hinv.1.trans hfuncs₂⟩, fun ws hws => ?_, fun htr => ?_,
      fun t hth => ?_⟩
    · rw [← hnr]
      exact flowOkE_tailFlow hfl hok₂ hob₂
    · obtain ⟨vs, hvs, rfl⟩ := tailFlow_retVals_inv hfl hws
      rw [← hnr, List.take_take, Nat.min_self]
      exact pre.trans (hret₂ vs hvs)
    · exact pre.trans (htr₂ (tailFlow_trap_inv hfl htr))
    · have hth' := tailFlow_throw_inv hfl hth
      subst hth'
      exact pre.trans (hT s₁ s₂ f a' fi₂ ps₂ rs₂ args t _ hS₁ hfi₂ hty₂ hargs hcr' hcall)

/-! ## The closure -/

/-- **The closure with pending tail calls on stores with the tag invariants**, as a call
oracle. -/
def closedP (tags : List TagInst) : Abstract.CallRel H :=
  fun s a us out => TagsOk tags s ∧ closedCallXP s a us out

/-- Restricting a run to an oracle defined on stores with the tag invariants. -/
theorem TagsOk.restrictP {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : ∀ s a us out, C s a us out → TagsOk tags s → TagsOk tags out.1)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) (hg : TagsOk tags s) :
    TagsOk tags r.1 ∧ EvalOXP (fun s a us out => TagsOk tags s ∧ C s a us out) s f stk es r :=
  EvalOXP.restrictI (I := TagsOk tags) (fun hf hi => hi.evalFlat hf)
    (fun ht he hn hi => tagsOk_throw hi ht he hn) hC h hg

/-- **The closure's answers on stores with the tag invariants are sound**, by least-fixpoint
induction. -/
theorem closedCallXP_sound (tags : List TagInst) :
    ∀ (s : Store H) a us out, closedCallXP s a us out → TagsOk tags s →
      SoundAnsE tags P host s a us out := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallXP s a us out ∧ (TagsOk tags s → SoundAnsE tags P host s a us out)
  have hQ : (closedCallXP : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us out ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩
    refine ⟨?_, fun hts => ?_⟩
    · rw [closedCallXP_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1,
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
  exact fun s a us out h hg => (hQ _ _ _ _ h).2 hg

theorem oracleSoundTE_closedP (tags : List TagInst) :
    OracleSoundTE (ehExt tags) P host (closedP (H := H) tags) true :=
  fun _ _ f _ fi ps rs _ _ c hS hfi hty hn hcr ⟨hg, hcl⟩ =>
    let h := (closedCallXP_sound (P := P) (host := host) tags _ _ _ _ hcl hg).2 f fi ps rs c hS hfi
      hty hn hcr
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem oracleThrowsE_closedP (tags : List TagInst) :
    OracleThrowsE (ehExt tags) P host (closedP (H := H) tags) :=
  fun _ _ f _ fi ps rs _ t c hS hfi hty hn hcr ⟨hg, hcl⟩ =>
    ((closedCallXP_sound (P := P) (host := host) tags _ _ _ _ hcl hg).2 f fi ps rs c hS hfi hty
      hn hcr).2.2.2 t rfl

theorem oracleTagsE_closedP (tags : List TagInst) : OracleTagsE tags (closedP (H := H) tags) :=
  fun _ _ _ _ _ ⟨hg, hcl⟩ _ =>
    (closedCallXP_sound (P := Numerics.Profile.spec) (host := default) tags _ _ _ _ hcl hg).1

/-- **Closed runs with pending tail calls are Core 3.0 runs**: on a store with the tag
invariants, every `EvalOXP` run against the closure `closedCallXP` of `ehExt`-checked code, all
call forms included, is a Core run with exceptions on; no oracle is assumed. -/
theorem evalOXP_closed_good {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP closedCallXP s f stk es r) (hg : TagsOk tags s) :
    TagsOk tags r.1 ∧ ArityGoodP (ehExt tags) s f stk es r true ∧
      CoreGoodP (ehExt tags) P host s f stk es r := by
  have hkeep : ∀ s a us out, closedCallXP s a us out → TagsOk tags s → TagsOk tags out.1 :=
    fun _ _ _ _ hcl hg => (closedCallXP_sound (P := P) (host := host) tags _ _ _ _ hcl hg).1
  exact evalOXP_goodP (oracleSoundTE_closedP tags) (oracleThrowsE_closedP tags)
    (oracleTagsE_closedP tags) (TagsOk.restrictP hkeep h hg).2 hg

end Silmaril.Wasm.Interp
