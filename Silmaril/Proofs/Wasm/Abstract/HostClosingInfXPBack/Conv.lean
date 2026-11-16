module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Closed
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
public import Silmaril.Games.Abstract.Module.Thms

/-!
# Closed canonical runs are logged runs resolving to no import call (proofs)

The converse of reading a logged run whose calls resolve to no import call as a closed run
(`HostClosingXP.evalLXPh_evRun` at the closed host): a run of the closed canonical semantics
`EvalOXP closedCallXP` that does not trap is a logged run `EvalLXPh` with the same result whose
calls the closure `Shape.close wasmHOpenXP` resolves to the empty log (`closed_conv`).

* `GoodAns`: a call answer the closure gives with the empty log: returned values (as the caller
  reads them, `retVals`, the callee's result arity taken) and an uncaught exception;
* `conv`: a non-trapping run of `EvalOXP C`, every answer of `C` good, is such a logged run. A
  trapping answer only ever ends the run in a trap, so it is never needed;
* `tail_wf`: the callee of a pending tail call is a function of the result's store, of a type
  whose result arity is the tail call's;
* `closed_good`: every answer of `closedCallXP` is good, by least-fixpoint induction: a body run is
  converted (`conv`), and the closure has its flow end, or its pending tail call answered by the
  tail callee's good answer (`tailAns`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Binaryen (BExpr liftInstrs Flow)

variable {H : Type}

/-- The closure of the canonical open module. -/
abbrev Cl : (wasmHShape H).ClosedMod := Shape.close wasmHOpenXP

/-- **An answer the closure gives with the empty log**: returned values, read by the caller with
the callee's result arity, and an uncaught exception. -/
def GoodAns (s : Store H) (a : Nat) (us : List Val) (out : Store H × Flow) : Prop :=
  (∀ vs, out.2.retVals = some vs → ∀ (fi : FuncInst H) (ps rs : List Validation.CValType),
    s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    (([] : List (Call (wasmHostSig H))), End.ret (.inl (vs.take rs.length).reverse) out.1) ∈
      Cl a s us) ∧
  (∀ t, out.2 = .throw t → (([] : List (Call (wasmHostSig H))), End.ret (.inr t) out.1) ∈ Cl a s us)

/-! ## Resolutions to the empty log -/

theorem sp_app {u v : List (HCall H)} (hu : Shape.SubstPre Cl u []) (hv : Shape.SubstPre Cl v []) :
    Shape.SubstPre Cl (u ++ v) [] := by
  generalize hq : ([] : List (Call (wasmHostSig H))) = q at hu
  induction hu with
  | nil => simpa using hv
  | ext _ _ => cases hq
  | @int g a s b s' rest c₁ q hm hr ih =>
    have hc : c₁ = [] ∧ q = [] := List.append_eq_nil_iff.mp hq.symm
    obtain ⟨rfl, rfl⟩ := hc
    exact Shape.SubstPre.int (rest := rest ++ v) hm (ih rfl)

theorem sp_one {a : Nat} {us : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    (hz : (([] : List (Call (wasmHostSig H))), End.ret b s₂) ∈ Cl a s₁ us) :
    Shape.SubstPre Cl ([OCall.mk a us s₁ b s₂].map OCall.lift) [] := by
  have := Shape.SubstPre.int (rest := []) hz (Shape.SubstPre.nil (c := Cl))
  rw [List.append_nil] at this
  exact this

theorem sp_mid {l₁ l₂ : List (OCall H)} {a : Nat} {us : List Val} {s₁ s₂ : Store H}
    {b : List Val ⊕ Nat} (h₁ : Shape.SubstPre Cl (l₁.map OCall.lift) [])
    (hz : (([] : List (Call (wasmHostSig H))), End.ret b s₂) ∈ Cl a s₁ us)
    (h₂ : Shape.SubstPre Cl (l₂.map OCall.lift) []) :
    Shape.SubstPre Cl ((l₁ ++ OCall.mk a us s₁ b s₂ :: l₂).map OCall.lift) [] := by
  rw [show l₁ ++ OCall.mk a us s₁ b s₂ :: l₂ = l₁ ++ [OCall.mk a us s₁ b s₂] ++ l₂ by simp,
    List.map_append, List.map_append]
  exact sp_app (sp_app h₁ (sp_one hz)) h₂

theorem sp_app' {l₁ l₂ : List (OCall H)} (h₁ : Shape.SubstPre Cl (l₁.map OCall.lift) [])
    (h₂ : Shape.SubstPre Cl (l₂.map OCall.lift) []) :
    Shape.SubstPre Cl ((l₁ ++ l₂).map OCall.lift) [] := by
  rw [List.map_append]; exact sp_app h₁ h₂

theorem nt_of_blockVals {fl : Flow} {vs : List Val} (h : fl.blockVals = some vs) :
    POut.flow fl ≠ .flow .trap := by
  rintro ⟨⟩; simp [Flow.blockVals] at h

/-! ## The conversion -/

/-- **A non-trapping run of `EvalOXP C`, every answer of `C` good, is a logged run resolving to
the empty log.** -/
theorem conv {C : CallRel H} (hC : ∀ s a us out, C s a us out → GoodAns s a us out)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP C s f stk es r) :
    r.2.2 ≠ .flow .trap → ∃ l, EvalLXPh s f stk es l r ∧ Shape.SubstPre Cl (l.map OCall.lift) [] := by
  induction h with
  | nil => exact fun _ => ⟨[], .nil, .nil⟩
  | argsAbort _ ho ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .argsAbort d ho, hl⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    have hz := (hC _ _ _ _ hcall).1 vs hvs fi ps rs (Interp.funcs_of_func? hfi) hty
    exact ⟨_, .callRet (ws := (vs.take rs.length).reverse) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂), sp_mid h₁ hz h₂⟩
  | callTrap => exact fun hn => (hn rfl).elim
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih =>
    intro _
    obtain ⟨l₁, d₁, h₁⟩ := ih (by simp)
    have hz := (hC _ _ _ _ hcall).2 t rfl
    exact ⟨_, .callThrow (s₂ := s₂) d₁ hfi hty, sp_app' h₁ (sp_one hz)⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .opOk hi d₁ hflat d₂, sp_app' h₁ h₂⟩
  | opStop hi _ hflat hfl ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .opStop hi d hflat hfl, hl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (nt_of_blockVals hvs)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .blockOk har d₁ hvs d₂, sp_app' h₁ h₂⟩
  | blockBrk har _ ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .blockBrk har d, hl⟩
  | blockEsc har _ ho ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .blockEsc har d ho, hl⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .loopOk har d₁ d₂, sp_app' h₁ h₂⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .loopBack har d₁ d₂, sp_app' h₁ h₂⟩
  | loopBrk har _ ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .loopBrk har d, hl⟩
  | loopEsc har _ ho ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .loopEsc har d ho, hl⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ (nt_of_blockVals hvs)
    obtain ⟨l₃, d₃, h₃⟩ := ih₃ hn
    exact ⟨_, .ifOk d₁ hb har d₂ hvs d₃, sp_app' (sp_app' h₁ h₂) h₃⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro _
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ (by simp)
    exact ⟨_, .ifBrk d₁ hb har d₂, sp_app' h₁ h₂⟩
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .ifEsc d₁ hb har d₂ ho, sp_app' h₁ h₂⟩
  | ifAbort _ ho ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .ifAbort d ho, hl⟩
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r _ hres hfi hty hy hcall
      hvs _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    have hz := (hC _ _ _ _ hcall).1 vs hvs fi ps rs hfi hty
    exact ⟨_, .indRet (ws := (vs.take rs.length).reverse) d₁ hres hfi hty hy
      (by rw [List.reverse_reverse]; exact d₂), sp_mid h₁ hz h₂⟩
  | callIndRes => exact fun hn => (hn rfl).elim
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl _ hres hfi hty hy hcall
      hfl ih =>
    intro hn
    cases fl with
    | trap => exact (hn rfl).elim
    | throw t =>
      obtain ⟨l₁, d₁, h₁⟩ := ih (by simp)
      have hz := (hC _ _ _ _ hcall).2 t rfl
      exact ⟨_, .indThrow (s₂ := s₂) d₁ hres hfi hty hy, sp_app' h₁ (sp_one hz)⟩
    | _ => exact hfl.elim
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r _ hfi hty hy hcall hvs _ ih₁
      ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (by simp)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    have hz := (hC _ _ _ _ hcall).1 vs hvs fi ps rs hfi hty
    exact ⟨_, .refRet (ws := (vs.take rs.length).reverse) d₁ hfi hty hy
      (by rw [List.reverse_reverse]; exact d₂), sp_mid h₁ hz h₂⟩
  | callRefNull => exact fun hn => (hn rfl).elim
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl _ hfi hty hy hcall hfl ih =>
    intro hn
    cases fl with
    | trap => exact (hn rfl).elim
    | throw t =>
      obtain ⟨l₁, d₁, h₁⟩ := ih (by simp)
      have hz := (hC _ _ _ _ hcall).2 t rfl
      exact ⟨_, .refThrow (s₂ := s₂) d₁ hfi hty hy, sp_app' h₁ (sp_one hz)⟩
    | _ => exact hfl.elim
  | tail _ hres hfi hty hy ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .tail d hres hfi hty hy, hl⟩
  | tailRes => exact fun hn => (hn rfl).elim
  | throw _ ht he hn' ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .throw d ht he hn', hl⟩
  | throwRefNull => exact fun hn => (hn rfl).elim
  | throwRefExn _ ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .throwRefExn d, hl⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro hn
    obtain ⟨l₁, d₁, h₁⟩ := ih₁ (nt_of_blockVals hvs)
    obtain ⟨l₂, d₂, h₂⟩ := ih₂ hn
    exact ⟨_, .tryOk har d₁ hvs d₂, sp_app' h₁ h₂⟩
  | tryBrk har _ ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .tryBrk har d, hl⟩
  | tryEsc har _ ho hnt ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .tryEsc har d ho hnt, hl⟩
  | tryCatch har _ hc ih =>
    intro _; obtain ⟨l, d, hl⟩ := ih (by simp); exact ⟨l, .tryCatch har d hc, hl⟩
  | tryRethrow har _ hc ih =>
    intro hn; obtain ⟨l, d, hl⟩ := ih hn; exact ⟨l, .tryRethrow har d hc, hl⟩

/-- **The callee of a pending tail call is well typed**: a function of the result's store whose
result arity is the tail call's. -/
theorem tail_wf {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    ∀ a' args n, r.2.2 = .tail a' args n → ∃ (fi : FuncInst H) (ps rs : List Validation.CValType),
      r.1.funcs[a']? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      n = rs.length := by
  induction h with
  | tail _ _ hfi hty _ _ =>
    intro a' args n h
    simp only [POut.tail.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨_, _, _, hfi, hty, rfl⟩
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ _ _ _ _ ih => exact ih
  | opOk _ _ _ _ _ ih => exact ih
  | blockOk _ _ _ _ _ ih => exact ih
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ _ ih => exact ih
  | loopBack _ _ _ _ ih => exact ih
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ _ _ ih => exact ih
  | ifEsc _ _ _ _ _ _ ih => exact ih
  | ifAbort _ _ ih => exact ih
  | callIndOk _ _ _ _ _ _ _ _ _ ih => exact ih
  | callRefOk _ _ _ _ _ _ _ _ ih => exact ih
  | tryOk _ _ _ _ _ ih => exact ih
  | tryEsc _ _ _ _ ih => exact ih
  | _ => intro _ _ _ h; cases h

/-! ## Closed answers are good -/

theorem close_of_open' {a : Nat} {s : Store H} {us : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s us) (hs : Shape.Subst Cl x.1 x.2 y) : y ∈ Cl a s us := by
  show y ∈ Shape.close wasmHOpenXP a s us
  rw [← Shape.resolve_close]
  exact ⟨x, hx, hs⟩

theorem subst_nil {L : List (HCall H)} (h : Shape.SubstPre Cl L [])
    (e : End (Store H) (List Val ⊕ Nat)) : Shape.Subst Cl L e ([], e) := by
  generalize hq : ([] : List (Call (wasmHostSig H))) = q at h
  induction h with
  | nil => exact .nil (c := Cl) e
  | ext _ _ => cases hq
  | int hm _ ih =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hq.symm
    exact .int hm (ih rfl)

theorem subst_then {L M : List (HCall H)} {e : End (Store H) (List Val ⊕ Nat)}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (h : Shape.SubstPre Cl L [])
    (hm : Shape.Subst Cl M e y) : Shape.Subst Cl (L ++ M) e y := by
  generalize hq : ([] : List (Call (wasmHostSig H))) = q at h
  induction h with
  | nil => simpa using hm
  | ext _ _ => cases hq
  | int hm' _ ih =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hq.symm
    exact Shape.Subst.int hm' (ih rfl)

theorem exitFlow_retVals {fl : Flow} {vs : List Val} (n : Nat) (h : fl.retVals = some vs) :
    exitFlow n fl = some (.normal (vs.take n).reverse) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | t <;> simp_all [Flow.retVals, exitFlow]

/-- **Every answer of one round of answering calls by good answers is good.** -/
theorem body_good {s : Store H} {a : Nat} {us : List Val} {out : Store H × Flow}
    (h : bodyCallXP GoodAns s a us out) : GoodAns s a us out := by
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, hbody, hfr⟩ := h
  cases hfr with
  | @flow _ bfl =>
    refine ⟨fun vs hvs fi' ps' rs' hfi' hty' => ?_, fun t ht => ?_⟩
    · rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      obtain ⟨l, d, hl⟩ := conv (fun _ _ _ _ h => h) hbody (by
        rintro ⟨⟩; simp [Flow.retVals] at hvs)
      exact close_of_open' (.inl ⟨fi, fn, ps, rs, s₁, f₂, bfl, _, l, hfi, hcode, hty, d,
        exitFlow_retVals rs.length hvs, rfl⟩) (subst_nil hl _)
    · simp only at ht; subst ht
      obtain ⟨l, d, hl⟩ := conv (fun _ _ _ _ h => h) hbody (by rintro ⟨⟩)
      exact close_of_open' (.inl ⟨fi, fn, ps, rs, s₁, f₂, .throw t, .throw t, l, hfi, hcode, hty,
        d, rfl, rfl⟩) (subst_nil hl _)
  | @tail _ s₂ a' n args fl hcall hfl =>
    obtain ⟨l, d, hl⟩ := conv (fun _ _ _ _ h => h) hbody (by rintro ⟨⟩)
    obtain ⟨fi', ps', rs', hfi', hty', rfl⟩ := tail_wf hbody a' args n rfl
    have key : ∀ b, (([] : List (Call (wasmHostSig H))), End.ret b s₂) ∈ Cl a' s₁ args →
        (([] : List (Call (wasmHostSig H))), Abstract.tailAns rs.length rs'.length b s₂) ∈
          Cl a s us := by
      intro b hz
      refine close_of_open' (.inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', rs'.length, args, b, l,
        hfi, hcode, hty, d, rfl⟩)) ?_
      rw [List.map_append]
      refine subst_then hl ?_
      have := Shape.Subst.int (rest := []) hz
        (Shape.Subst.nil (c := Cl) (Abstract.tailAns rs.length rs'.length b s₂))
      exact this
    refine ⟨fun vs hvs fi₀ ps₀ rs₀ hfi₀ hty₀ => ?_, fun t ht => ?_⟩
    · rw [hfi] at hfi₀; cases hfi₀
      rw [hty] at hty₀; cases hty₀
      rcases fl with w | ⟨_ | k, w⟩ | w | _ | t <;>
        simp only [tailFlow, Flow.retVals, Option.some.injEq, reduceCtorEq] at hvs
      all_goals
        subst hvs
        have hz := (hcall.1 w (by simp [Flow.retVals]) fi' ps' rs' hfi' hty')
        have := key _ hz
        simpa [Abstract.tailAns, ansFlow, tailFlow, exitFlow, endOfFlow, List.take_take] using this
    · rcases fl with w | ⟨_ | k, w⟩ | w | _ | t' <;> simp only [tailFlow, reduceCtorEq] at ht
      simp only [Flow.throw.injEq] at ht
      subst ht
      have := key _ (hcall.2 _ rfl)
      simpa [Abstract.tailAns, ansFlow, tailFlow, exitFlow, endOfFlow] using this

/-- **Every answer of the closed call relation is good.** -/
theorem closed_good : ∀ s a us out, closedCallXP s a us out → GoodAns (H := H) s a us out :=
  OrderHom.lfp_le bodyCallXPOp (fun _ _ _ _ h => body_good h)

/-- **A non-trapping closed canonical run is a logged run resolving to the empty log.** -/
theorem closed_conv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP closedCallXP s f stk es r)
    (hn : r.2.2 ≠ .flow .trap) :
    ∃ l, EvalLXPh s f stk es l r ∧ Shape.SubstPre Cl (l.map OCall.lift) [] :=
  conv closed_good h hn

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
