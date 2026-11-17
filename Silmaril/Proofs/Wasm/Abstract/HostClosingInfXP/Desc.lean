module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.Reach
public import Silmaril.Wasm.Interp.OracleX.Thms

/-!
# Descents, and divergence after a log: canonical to Core (proofs)

* `descends_unwrap`: a descent of `wasmHOpenXP` is a logged reach in a Wasm body, or the body's
  run to a pending tail call, made at the frame;
* `enter_body`, `descends_fwd`, `descPath_fwd`: a descent (path) is a Core run from the caller's
  call, in its `call_ref` form inside an active context, into the callee's, its first step
  entering the caller's body host-free;
* `quiet_evalOXP`: a logged run whose calls resolve to no import call is a run of the closed
  semantics `EvalOXP closedCallXP` (at the closed host, `hostCallXP closedHost = closedCallXP`);
* `funDivXP_of_chain`: an infinite chain of host-free descents is host-free divergence of the
  first call (`FunDivXP`), by coinduction;
* `wasmEvFunDXP_div_evRun`: a divergent behaviour `(cs, div)` of `wasmEvFunDXP` whose log the
  host allows is a Core run of the invocation with exactly the host events `cs`, then host-free
  divergence: a descent path to a call diverging host-free (`diverges_of_funDivXP`), or to a call
  whose body diverges host-free after a log (`logDivXP_fwd`, `diverges_of_evalDivXP`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP DivStepXP CallStepXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Logs -/

theorem lift_eq_mk {z : OCall H} {g : Nat} {a : List Val} {s : Store H}
    {ans : (List Val ⊕ Nat) × Store H}
    (h : OCall.lift z = ⟨.inr ⟨g, (a, s)⟩, ans⟩) : z = OCall.mk g a s ans.1 ans.2 := by
  rcases z with ⟨⟨⟩ | ⟨g', a', s'⟩, ⟨b, s₂⟩⟩
  cases h
  rfl

/-- A log whose lift splits at an internal call splits there. -/
theorem map_lift_split {l : List (OCall H)} {u w : List (HCall H)} {y : (wasmOShape H).self.Op}
    {ans : (List Val ⊕ Nat) × Store H}
    (h : l.map OCall.lift = u ++ ⟨.inr y, ans⟩ :: w) :
    ∃ l₁ l₂, l = l₁ ++ OCall.mk y.1 y.2.1 y.2.2 ans.1 ans.2 :: l₂ ∧ l₁.map OCall.lift = u := by
  obtain ⟨l₁, l₂', rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  obtain ⟨z, l₂, rfl, hz, -⟩ := List.map_eq_cons_iff.mp h₂
  exact ⟨l₁, l₂, by rw [lift_eq_mk hz], h₁⟩

theorem mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' s₂ s₂' : Store H}
    {b b' : List Val ⊕ Nat} (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem split_last {α : Type} {la l₁ l₂ : List α} {x z : α} (h : la ++ [x] = l₁ ++ z :: l₂) :
    (∃ m, la = l₁ ++ z :: m) ∨ (l₁ = la ∧ z = x) := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · rcases a' with _ | ⟨y, a'⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at h₁ h₂
      exact .inr ⟨h₁, h₂.1.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at h₂
      exact absurd h₂.2 (by simp)
  · rcases c' with _ | ⟨z', c''⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at h₁ h₂
      exact .inr ⟨h₁.symm, h₂.1⟩
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, -⟩ := h₂
      exact .inl ⟨c'', h₁⟩

/-- **A descent of `wasmHOpenXP` is a logged reach in a Wasm body, or the body's run to a
pending tail call to the callee.** -/
theorem descends_unwrap {c : (wasmHShape H).ClosedMod} {x y : (wasmHShape H).self.Op}
    {q : List (Call (wasmHostSig H))} (h : Shape.Descends wasmHOpenXP c x q y) :
    ∃ (fi : FuncInst H) (fn : Func) (l : List (OCall H)), x.2.2.funcs[x.1]? = some fi ∧
      fi.code = .wasm fn ∧ SubstPre c (l.map OCall.lift) q ∧
      (ReachLXP x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body)
          l y ∨
        ∃ (f₂ : Frame) (n : Nat), EvalLXPh x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) []
          (Binaryen.liftInstrs fn.body) l (y.2.2, f₂, .tail y.1 y.2.1 n)) := by
  obtain ⟨z, hz, u, ans, rest, he, hq⟩ := h
  rcases hz with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, -, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, hc, hty, hE, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, -, -, -, -, rfl⟩
  · obtain ⟨l₁, l₂, rfl, rfl⟩ := map_lift_split he
    exact ⟨fi, fn, l₁, hfi, hc, hq, .inl (reachLXP_of_evalLXPh hE rfl)⟩
  · obtain ⟨l₁, l₂, hl, rfl⟩ := map_lift_split he
    rcases split_last hl with ⟨m, h₁⟩ | ⟨rfl, h₁⟩
    · exact ⟨fi, fn, l₁, hfi, hc, hq, .inl (reachLXP_of_evalLXPh hE h₁)⟩
    · obtain ⟨h₁, h₂, h₃⟩ := mk_inj h₁
      obtain ⟨y₁, y₂, y₃⟩ := y
      dsimp only at h₁ h₂ h₃
      subst h₁ h₂ h₃
      exact ⟨fi, fn, _, hfi, hc, hq, .inr ⟨f₂, n, hE⟩⟩
  · rcases u with _ | ⟨_, u⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨he, -⟩ := he
      cases he
    · have := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega

/-! ## Calls inside contexts -/

/-- **The call `y` in its `call_ref` form inside an active context**, in some frame. -/
def AtCall (y : (wasmOShape H).self.Op) (c : Config H) : Prop :=
  ∃ (E : Sim.ActiveCtx) (F : Frame) (pre : List Val) (c₀ : Admin) (rest : List Admin),
    c₀.IsCallRef ∧ c = E.plug ⟨y.2.2, F, Interp.callCode pre y.2.1 y.1 c₀ rest⟩

theorem atCall_of_hole {tags : List TagInst} {y : (wasmOShape H).self.Op} {E : Sim.ActiveCtx}
    {c : Config H} (h : CallHole tags y c) : AtCall y (E.plug c) ∧ CallChkP tags y.2.2 y.1 y.2.1 := by
  obtain ⟨F, pre, c₀, rest, hcr, rfl, hcc⟩ := h
  exact ⟨⟨E, F, pre, c₀, rest, hcr, rfl⟩, hcc⟩

section Enter

variable {tags : List TagInst}

/-- The check of a Wasm callee's body, in its frame. -/
theorem body_chk {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} (hS : StoreChkE (ehExt tags) s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    ∃ ob, chkE (ehExt tags) s.funcs (Frame.forCall fi.module us fn.locals).module
        (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
  obtain ⟨ob, hb, -⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  exact ⟨ob, by rw [hlen]; exact hb⟩

/-- **Entering a Wasm callee** from its `call_ref` form in an active context: one host-free
step to its body, in its frame and label. -/
theorem enter_body {y : (wasmOShape H).self.Op} {E : Sim.ActiveCtx} {F : Frame} {pre : List Val}
    {c₀ : Admin} {rest : List Admin} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hcr : c₀.IsCallRef) (hfi : y.2.2.funcs[y.1]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : y.2.1.length = ps.length) :
    Step P NH (E.plug ⟨y.2.2, F, Interp.callCode pre y.2.1 y.1 c₀ rest⟩)
      ((Sim.ActiveCtx.label rs.length [] [] [] (.frame rs.length F pre rest E)).plug
        ⟨y.2.2, Frame.forCall fi.module y.2.1 fn.locals, xcode [] (Binaryen.liftInstrs fn.body)⟩) := by
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have st := Step.callRefFunc (P := P) (host := NH) (f := F) hcr hfi hex (hn.trans hpl.symm) hcode
  have st' := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH) pre rest st
  refine Sim.ActiveCtx.step E ?_
  simp only [xcode, Binaryen.lowerList_liftInstrs, Interp.callCode]
  rw [← hrl]
  simpa [vals] using st'

end Enter

section Fwd

variable {tags : List TagInst} (hH : HostSliceT host) (hE : HostSliceE tags host)
include hH hE

/-- **A descent is a Core run from the caller's call into the callee's**, with exactly the
import calls of the descent, its first step host-free; the callee's call is checked. -/
theorem descends_fwd {x y : (wasmHShape H).self.Op} {q : List (Call (wasmHostSig H))}
    (hd : Shape.Descends wasmHOpenXP (Shape.close wasmHOpenXP) x q y) (hc : Cons host q)
    (hx : CallChkP tags x.2.2 x.1 x.2.1) {c : Config H} (hat : AtCall x c) :
    ∃ c₁ c₂, Step P NH c c₁ ∧ EvRun P host c₁ q c₂ ∧ AtCall y c₂ ∧
      CallChkP tags y.2.2 y.1 y.2.1 := by
  obtain ⟨hS, hts, fi', ps, rs, hfi', hty, hn⟩ := hx
  obtain ⟨E, F, pre, c₀, rest, hcr, rfl⟩ := hat
  obtain ⟨fi, fn, l, hfi, hcode, hq, hk⟩ := descends_unwrap hd
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨ob, hbc⟩ := body_chk hS hfi hcode hty hn
  have st := enter_body (P := P) (E := E) (F := F) (pre := pre) (rest := rest) hcr hfi hcode hty hn
  rcases hk with hr | ⟨f₂, n, hEv⟩
  · obtain ⟨E', c', run, hT⟩ := reachLXP_fwd (P := P) hH hE hr q hq hc _ _ _ hts hS hbc
    obtain ⟨hat', hcc⟩ := atCall_of_hole (E := actComp E' _) hT
    refine ⟨_, _, st, ?_, hat', hcc⟩
    rw [plug_actComp]
    exact evRun_plug _ run
  · obtain ⟨t₁, hA, cl⟩ := full_run (P := P) hH hE hEv hq hc hts
    obtain ⟨hok, hinv, hw⟩ := hA hS hbc
    obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := hw _ _ _ rfl
    obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
    have hS₁ : StoreChkE (ehExt tags) y.2.2.funcs := hinv.1.2.1 hS
    obtain ⟨s'', f'', c', o, hrun, he, hm⟩ := cl hS hbc
    obtain ⟨vs₁, c₁, rfl, hc₁, hs'', hf''⟩ := matchP_tail_iff.mp hm
    subst s'' f''
    obtain ⟨-, rest', rfl⟩ := he
    have inner := evRun_plug (Sim.ActiveCtx.label rs.length [] [] [] (.frame rs.length F pre rest E))
      hrun
    have ex := frame_tail_exit (P := P) (host := NH) (s := y.2.2) (f := F) (k := rs.length)
      (F := f₂) (vs₁ := vs₁) (rest := rest') hc₁ hfi₂ hex₂ (hargs.trans hpl₂.symm)
    have ex' := evRun_plug (host := host) E
      (evRun_of_free (Steps.ctx (P := P) (host := NH) pre rest ex))
    refine ⟨_, _, st, ?_, ⟨E, F, pre, c₁.retToCallIn f₂.module, rest,
      isCallRef_retToCallIn hc₁ _, rfl⟩, hS₁, t₁, fi₂, ps₂, rs₂, hfi₂, hty₂, hargs⟩
    have e1 : (Sim.ActiveCtx.label rs.length [] [] [] (.frame rs.length F pre rest E)).plug
        ⟨y.2.2, f₂, vals (vs₁ ++ y.2.1) ++ .ref (.func y.1) :: c₁ :: rest'⟩ =
        E.plug ⟨y.2.2, F, vals pre ++ [.frame rs.length f₂ [.label rs.length []
          (vals (vs₁ ++ y.2.1) ++ .ref (.func y.1) :: c₁ :: rest')]] ++ rest⟩ := by
      simp [Sim.ActiveCtx.plug, vals]
    rw [e1] at inner
    have := evRun_trans inner ex'
    rw [List.append_nil] at this
    exact this

/-- **A descent path is a Core run from the first call into the last**, with exactly its import
calls; the last call is checked. -/
theorem descPath_fwd {x z : (wasmHShape H).self.Op} {qs : List (Call (wasmHostSig H))}
    (h : Shape.DescPath wasmHOpenXP (Shape.close wasmHOpenXP) x qs z) :
    Cons host qs → CallChkP tags x.2.2 x.1 x.2.1 → ∀ {c : Config H}, AtCall x c →
      ∃ c', EvRun P host c qs c' ∧ AtCall z c' ∧ CallChkP tags z.2.2 z.1 z.2.1 := by
  induction h with
  | refl x => exact fun _ hx c hat => ⟨c, .refl _, hat, hx⟩
  | step hd _ ih =>
    intro hc hx c hat
    rw [cons_append] at hc
    obtain ⟨c₁, c₂, st, run, hat₂, hy⟩ := descends_fwd hH hE hd hc.1 hx hat
    obtain ⟨c', run', hat', hz⟩ := ih hc.2 hy hat₂
    exact ⟨c', evRun_trans (.silent (.inl st) run) run', hat', hz⟩

end Fwd

/-! ## Host-free descents are closed divergence -/

theorem hostSliceT_closed : HostSliceT (Binaryen.closedHost : HostSemantics H) where
  funcs _ _ _ _ _ hr := hr.elim
  arity _ _ _ _ _ _ _ _ _ _ _ _ hr := hr.elim

theorem hostSliceE_closed (tags : List TagInst) :
    HostSliceE tags (Binaryen.closedHost : HostSemantics H) where
  chk _ _ _ _ _ hr := hr.elim
  tags _ _ _ _ _ hr := hr.elim

/-- **A logged run whose calls resolve to no import call is a run of the closed semantics.** -/
theorem quiet_evalOXP {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r)
    (hq : SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) []) :
    EvalOXP closedCallXP s f stk es r := by
  have := (evalLXPh_evRun (P := Silmaril.Wasm.Numerics.Profile.spec) (tags := [])
    hostSliceT_closed (hostSliceE_closed []) h hq (fun _ h => nomatch h)).1
  rwa [HostEvalP.hostCallXP_closedHost] at this

theorem substPre_nil_split {la lb : List (OCall H)}
    (hq : SubstPre (Shape.close wasmHOpenXP) ((la ++ lb).map OCall.lift) []) :
    SubstPre (Shape.close wasmHOpenXP) (la.map OCall.lift) [] ∧
      SubstPre (Shape.close wasmHOpenXP) (lb.map OCall.lift) [] := by
  rw [List.map_append] at hq
  obtain ⟨q₁, q₂, e, h₁, h₂⟩ := substPre_append.1 hq
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp e.symm
  exact ⟨h₁, h₂⟩

theorem substPre_nil_mid {la lb : List (OCall H)} {z : OCall H}
    (hq : SubstPre (Shape.close wasmHOpenXP) ((la ++ z :: lb).map OCall.lift) []) :
    SubstPre (Shape.close wasmHOpenXP) ((la ++ [z]).map OCall.lift) [] ∧
      SubstPre (Shape.close wasmHOpenXP) (lb.map OCall.lift) [] := by
  rw [show la ++ z :: lb = (la ++ [z]) ++ lb by simp] at hq
  exact substPre_nil_split hq

/-- The code side of an infinite host-free descent chain: a host-free reach to a call of it. -/
def ChainX (g : Nat → (wasmOShape H).self.Op) : Interp.Problem H := fun s f stk es =>
  ∃ (l : List (OCall H)) (z : (wasmOShape H).self.Op), ReachLXP s f stk es l z ∧
    SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) [] ∧ ∃ n, g n = z

/-- The calls of an infinite host-free descent chain. -/
def ChainY (g : Nat → (wasmOShape H).self.Op) : XDivergeP.CallProblem H := fun s a vs =>
  ∃ n, g n = ⟨a, (vs, s)⟩

theorem chainX_step {g : Nat → (wasmOShape H).self.Op} {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} (h : ChainX g s f stk es) :
    DivStepXP (ChainX g) (ChainY g) s f stk es := by
  obtain ⟨l, z, hr, hq, n, hn⟩ := h
  cases hr with
  | call hargs hfi hty => exact .callee (quiet_evalOXP hargs hq) hfi hty ⟨n, hn⟩
  | ind hargs hres hfi hty hy =>
    exact .callIndCallee (quiet_evalOXP hargs hq) hres hfi hty hy ⟨n, hn⟩
  | ref hargs hfi hty hy => exact .callRefCallee (quiet_evalOXP hargs hq) hfi hty hy ⟨n, hn⟩
  | args hr => exact .args ⟨_, _, hr, hq, n, hn⟩
  | callK hargs hfi hty hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_mid hq
    exact .cont (quiet_evalOXP (.callRet hargs hfi hty .nil) h₁) ⟨_, _, hr, h₂, n, hn⟩
  | indK hargs hres hfi hty hy hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_mid hq
    exact .cont (quiet_evalOXP (.indRet hargs hres hfi hty hy .nil) h₁) ⟨_, _, hr, h₂, n, hn⟩
  | refK hargs hfi hty hy hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_mid hq
    exact .cont (quiet_evalOXP (.refRet hargs hfi hty hy .nil) h₁) ⟨_, _, hr, h₂, n, hn⟩
  | opK hi hargs hflat hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    have hE' := EvalLXPh.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE'
    exact .cont (quiet_evalOXP hE' h₁) ⟨_, _, hr, h₂, n, hn⟩
  | block har hr => exact .block har ⟨_, _, hr, hq, n, hn⟩
  | blockK har hbody hvs hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    have hE' := EvalLXPh.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact .cont (quiet_evalOXP hE' h₁) ⟨_, _, hr, h₂, n, hn⟩
  | loop har hr => exact .loop har ⟨_, _, hr, hq, n, hn⟩
  | loopK har hbody hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    have hE' := EvalLXPh.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE'
    exact .cont (quiet_evalOXP hE' h₁) ⟨_, _, hr, h₂, n, hn⟩
  | loopBack har hbody hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    exact .loopBack har (quiet_evalOXP hbody h₁) ⟨_, _, hr, h₂, n, hn⟩
  | cond hr => exact .cond ⟨_, _, hr, hq, n, hn⟩
  | arm hcE hb har hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    exact .arm (quiet_evalOXP hcE h₁) hb har ⟨_, _, hr, h₂, n, hn⟩
  | ifK hcE hb har harm hvs hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    have hE' := EvalLXPh.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact .cont (quiet_evalOXP hE' h₁) ⟨_, _, hr, h₂, n, hn⟩
  | handler har hr => exact .try_ har ⟨_, _, hr, hq, n, hn⟩
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ _ har hbody hvs hr =>
    obtain ⟨h₁, h₂⟩ := substPre_nil_split hq
    have hE' := EvalLXPh.tryOk (cs := cs) har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    exact .cont (quiet_evalOXP hE' h₁) ⟨_, _, hr, h₂, n, hn⟩

/-- **An infinite chain of host-free descents is host-free divergence of its first call.** -/
theorem funDivXP_of_chain (g : Nat → (wasmOShape H).self.Op)
    (hd : ∀ n, Shape.Descends wasmHOpenXP (Shape.close wasmHOpenXP) (g n) [] (g (n + 1))) :
    FunDivXP (g 0).2.2 (g 0).1 (g 0).2.1 := by
  refine (XDivergeP.evalDivXP_of_coind (X := ChainX g) (Y := ChainY g)
    (fun _ _ _ _ h => chainX_step h) ?_).2 _ _ _ ⟨0, rfl⟩
  rintro s a vs ⟨n, hn⟩
  have hdn := hd n
  rw [hn] at hdn
  obtain ⟨fi, fn, l, hfi, hcode, hq, hr | ⟨f₂, k, hEv⟩⟩ := descends_unwrap hdn
  · exact .body hfi hcode ⟨l, _, hr, hq, n + 1, rfl⟩
  · exact .frameTail hfi hcode (quiet_evalOXP hEv hq) ⟨n + 1, rfl⟩

/-! ## Divergence after a log -/

theorem descPath_snoc {m : (wasmHShape H).OpenMod} {c : (wasmHShape H).ClosedMod}
    {x y z : (wasmHShape H).self.Op} {qs q : List (Call (wasmHostSig H))}
    (h : Shape.DescPath m c x qs y) (hd : Shape.Descends m c y q z) :
    Shape.DescPath m c x (qs ++ q) z := by
  induction h with
  | refl => simpa using Shape.DescPath.step hd (.refl _)
  | step h' _ ih => simpa [List.append_assoc] using Shape.DescPath.step h' (ih hd)

theorem descPath_of_chain {m : (wasmHShape H).OpenMod} {c : (wasmHShape H).ClosedMod}
    (g : Nat → (wasmHShape H).self.Op) (q : Nat → List (Call (wasmHostSig H)))
    (hd : ∀ n, Shape.Descends m c (g n) (q n) (g (n + 1))) :
    ∀ N, Shape.DescPath m c (g 0) ((List.range N).flatMap q) (g N) := by
  intro N
  induction N with
  | zero => exact .refl _
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    simpa using descPath_snoc ih (hd N)

theorem invoke_atCall {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hfi : s.funcs[a]? = some fi) : AtCall ⟨a, (vs, s)⟩ (invoke s a vs) :=
  ⟨.hole, {}, [], .callRefType fi.type, [], trivial, by
    simp [invoke, hfi, Sim.ActiveCtx.plug, Interp.callCode, vals]⟩

theorem invoke_callChk {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ∃ fi : FuncInst H, s.funcs[a]? = some fi ∧ CallChkP tags s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  exact ⟨fi, hfi, hS, hts, fi, _, _, hfi, hty, hvs.length_eq⟩

/-- **Divergence after a log is a Core run with exactly that log, then host-free divergence.** -/
theorem wasmEvFunDXP_div_evRun {tags : List TagInst} (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (hc : Cons host cs) :
    ∃ c', EvRun P host (invoke s a vs) cs c' ∧ Diverges P NH c' := by
  obtain ⟨fi, hfi, hx⟩ := invoke_callChk hS hts hok
  have hat := invoke_atCall (vs := vs) hfi
  rcases h with (h | ⟨-, g, q, N, hg0, hdesc, hN, hcs⟩) | ⟨-, z, qs, u, q', hpath, hldl, hsub, hcs⟩
  · exact absurd h wasmEvFunXP_ne_div
  · have hcs' : cs = (List.range N).flatMap q := hcs
    subst hcs'
    have hpath := descPath_of_chain g q hdesc N
    rw [hg0] at hpath
    obtain ⟨c', run, ⟨E, F, pre, c₀, rest, hcr, rfl⟩, hcc⟩ :=
      descPath_fwd (P := P) hH hE hpath hc hx hat
    have hfun := funDivXP_of_chain (fun k => g (N + k)) (fun k => by
      have := hdesc (N + k)
      rw [hN (N + k) (Nat.le_add_right N k)] at this
      simpa [Nat.add_assoc] using this)
    exact ⟨_, run, diverges_of_funDivXP (P := P) (host := NH) hfun hcc hcr E⟩
  · have hcs' : cs = qs ++ q' := hcs
    subst hcs'
    rw [cons_append] at hc
    obtain ⟨fz, fn, l, hfz, hcode, hlog, rfl⟩ := hldl
    obtain ⟨c₁, run₁, ⟨E, F, pre, c₀, rest, hcr, rfl⟩, hcc⟩ :=
      descPath_fwd (P := P) hH hE hpath hc.1 hx hat
    obtain ⟨hSz, htz, fi', ps, rs, hfi', hty, hn⟩ := hcc
    obtain rfl : fi' = fz := Option.some.inj (hfi'.symm.trans hfz)
    obtain ⟨ob, hbc⟩ := body_chk hSz hfz hcode hty hn
    have st := enter_body (P := P) (E := E) (F := F) (pre := pre) (rest := rest) hcr hfz hcode hty hn
    obtain ⟨E', c', run₂, s', f', stk', es', rfl, hdiv, hchk⟩ :=
      logDivXP_fwd (P := P) hH hE hlog q' hsub hc.2 _ _ _ htz hSz hbc
    refine ⟨_, evRun_trans run₁ (.silent (.inl st) (evRun_plug _ run₂)), ?_⟩
    rw [← plug_actComp]
    exact diverges_of_evalDivXP hdiv hchk _

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP
