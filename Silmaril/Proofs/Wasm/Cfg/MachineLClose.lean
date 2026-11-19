module

public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Thms
public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
public import Silmaril.Games.Abstract.Module.Thms

@[expose] public section

/-!
# The session closure answers the logged machine's calls (proofs)

Proofs for `Silmaril.Wasm.Cfg.MachineLClose.Thms`.

* `close_good`: least-fixpoint induction on `Shape.close wasmHOpenXPS`. Every behaviour ends in
  `.ret` (the open module's ends are all `.ret`, and resolution keeps them), and a behaviour with
  the empty log is a `closedCallXP` answer (`CloseOk closedCallXP`). With the empty log, every
  call of the open behaviour is internal and resolved by a closure behaviour with the empty log
  (`subst_nil`), so by induction a `closedCallXP` answer. The body run is then an
  `EvalOXP closedCallXP` run (`closed_iff_logged`), which `closedCallXP_fixpoint` and
  `FrameP` turn into the answer (`open_closeOk`).
* `logged_of_session`: the body's check makes the run one of `EvalOXP (fitP closedCallXP)`
  (`TypedCatFit.evalOXP_closed_iff_fit`), so a logged run with `CloseOk (fitP closedCallXP)`
  entries (`closed_iff_logged`), which `MachineL.backward` reads as a machine run. A pending tail
  call fits by `MachineL.tail_fit_initialK`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLClose

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall wasmHShapeS wasmHOpenXPS wasmEvFunXPS endOfFlowS
  tailAnsS exitFlow ansFlow)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP FrameP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP closedCallXP_fixpoint)
open Silmaril.Wasm.Abstract.TypedCat (fitP ArgsFit arityResp_fitClosed)
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx)

variable {H : Type}

/-! ## Pending tail calls of the session relation -/

/-- **A pending tail call names a function of its result's store, at its result arity.** -/
theorem evalLXPS_tail_wf {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    ∀ a args n, r.2.2 = .tail a args n →
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), r.1.funcs[a]? = some fi ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧ n = rs.length := by
  induction h with
  | tail _ hres hfi hty hy _ =>
    intro a args n h
    cases h
    exact ⟨_, _, _, hfi, hty, rfl⟩
  | _ => first | (intro a args n h; cases h; done) | assumption

/-! ## Ends of the open module -/

theorem endOfFlowS_ret (fl : Flow) (s : Store H) : ∃ b, endOfFlowS fl s = .ret b s := by
  cases fl <;> exact ⟨_, rfl⟩

theorem tailAnsS_ret (m n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (s : Store H) :
    ∃ b', tailAnsS m n b s = .ret b' s := by
  rcases b with b | u
  · simp only [tailAnsS]
    split
    · exact endOfFlowS_ret _ _
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Every behaviour of the open module ends in `.ret`. -/
theorem open_ret {g : Nat} {s : Store H} {a : List Val}
    {x : CallBeh ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self) (Store H)
      ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hx : x ∈ wasmHOpenXPS g s a) : ∃ b s₂, x.2 = .ret b s₂ := by
  rcases hx with ⟨-, -, -, -, s', -, -, fl, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, rs, -, s₂, -, -, n, -, b, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, s', -, fl, -, -, -, -, rfl⟩
  · obtain ⟨b, hb⟩ := endOfFlowS_ret fl s'; exact ⟨b, s', hb⟩
  · obtain ⟨b', hb⟩ := tailAnsS_ret rs.length n b s₂; exact ⟨b', s₂, hb⟩
  · obtain ⟨b, hb⟩ := endOfFlowS_ret fl s'; exact ⟨b, s', hb⟩

/-! ## Resolution -/

/-- Resolution against a module whose behaviours all end in `.ret` keeps `.ret` ends. -/
theorem subst_ret {c : (wasmHShapeS H).ClosedMod}
    (hc : ∀ g s a y, y ∈ c g s a → ∃ b s₂, y.2 = End.ret b s₂)
    {l : List (Call ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self))}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hs : Shape.Subst c l e y) (he : ∃ b s₂, e = .ret b s₂) :
    ∃ b s₂, y.2 = .ret b s₂ := by
  induction hs with
  | nil e => exact he
  | ext _ ih => exact ih he
  | int _ _ ih => exact ih he
  | intTrap h => obtain ⟨_, _, h'⟩ := hc _ _ _ _ h; cases h'
  | intDiv h => obtain ⟨_, _, h'⟩ := hc _ _ _ _ h; cases h'

/-- **Resolution to the empty log**: every call is internal, resolved by a callee behaviour with
the empty log, and the end is the open end. -/
theorem subst_nil {c : (wasmHShapeS H).ClosedMod}
    {l : List (Call ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self))}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hs : Shape.Subst c l e y) :
    ∀ b s₂, y = ([], .ret b s₂) → e = .ret b s₂ ∧
      ∀ z ∈ l, ∃ (g : Nat) (a : List Val) (s : Store H)
        (b' : (List Val ⊕ Nat) ⊕ PUnit.{1}) (s' : Store H),
        z = SCall.mk g a s b' s' ∧ ([], .ret b' s') ∈ c g s a := by
  induction hs with
  | nil e =>
    intro b s₂ h
    cases h
    exact ⟨rfl, fun z hz => by cases hz⟩
  | ext _ _ =>
    intro b s₂ h
    cases h
  | @int g a s b' s' rest e c₁ y hc _ ih =>
    intro b s₂ h
    obtain ⟨hy₁, hy₂⟩ := Prod.mk.inj h
    obtain ⟨rfl, hy₁⟩ := List.append_eq_nil_iff.mp hy₁
    obtain ⟨he, hrest⟩ := ih b s₂ (Prod.ext hy₁ hy₂)
    refine ⟨he, fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨g, a, s, b', s', rfl, hc⟩
    · exact hrest z hz
  | intTrap _ =>
    intro b s₂ h
    cases h
  | intDiv _ =>
    intro b s₂ h
    cases h

/-! ## Open behaviours with `closedCallXP`-answered calls -/

theorem closeOk_vals {C : Abstract.CallRel H} {g : Nat} {a : List Val} {s s₂ : Store H}
    {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow} {vs : List Val}
    (hfi : s.funcs[g]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hC : C s g a (s₂, fl)) (hvs : fl.retVals = some vs) :
    CloseOk C (SCall.mk g a s (.inl (.inl (vs.take rs.length).reverse)) s₂) :=
  ⟨fi, ps, rs, fl, vs, hfi, hty, hC, hvs, rfl⟩

/-- **An open behaviour whose calls are `closedCallXP` answers is a `closedCallXP` answer.** -/
theorem open_closeOk {g : Nat} {s s₂ : Store H} {a : List Val}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}}
    {x : CallBeh ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self) (Store H)
      ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hx : x ∈ wasmHOpenXPS g s a) (hend : x.2 = .ret b s₂)
    (hl : ∀ z ∈ x.1, CloseOk closedCallXP z) :
    CloseOk closedCallXP (SCall.mk g a s b s₂) := by
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hcode, hty, hrun, hex, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂', f₂, a', n, args, b', l, hfi, hcode, hty, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hcode, hty, hex, rfl⟩
  · have hO : EvalOXP closedCallXP s (Frame.forCall fi.module a fn.locals) []
        (liftInstrs fn.body) (s', f₂, .flow bfl) := closed_iff_logged.mpr ⟨l, hrun, hl⟩
    have hC : closedCallXP s g a (s', bfl) := by
      rw [closedCallXP_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, s', .flow bfl, hfi, hcode, hty, hO, .flow⟩
    simp only at hend
    rcases bfl with w | ⟨_ | j, w⟩ | w | _ | t <;>
      simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hex <;> subst hex <;>
      simp only [endOfFlowS, End.ret.injEq] at hend <;> obtain ⟨rfl, rfl⟩ := hend
    · exact closeOk_vals hfi hty hC rfl
    · exact closeOk_vals hfi hty hC rfl
    · exact closeOk_vals hfi hty hC rfl
    · exact hC
    · exact hC
  · have hl₁ : ∀ z ∈ l, CloseOk closedCallXP z := fun z hz =>
      hl z (List.mem_append_left _ hz)
    have hlast : CloseOk closedCallXP (SCall.mk a' args s₁ b' s₂') :=
      hl _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hO : EvalOXP closedCallXP s (Frame.forCall fi.module a fn.locals) []
        (liftInstrs fn.body) (s₁, f₂, .tail a' args n) :=
      closed_iff_logged.mpr ⟨l, hrun, hl₁⟩
    obtain ⟨fi', ps', rs', hfi', hty', hn⟩ := evalLXPS_tail_wf hrun a' args n rfl
    simp only at hfi'
    have hC : ∀ fl, closedCallXP s₁ a' args (s₂', fl) →
        ((∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) →
        closedCallXP s g a (s₂', Abstract.CallX.tailFlow n fl) := by
      intro fl hcall hfl
      rw [closedCallXP_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, s₁, .tail a' args n, hfi, hcode, hty, hO, .tail hcall hfl⟩
    simp only at hend
    rcases b' with (ws | t) | u
    · obtain ⟨fi'', ps'', rs'', fl, vs, hfi'', hty'', hcall, hvs, rfl⟩ := hlast
      rw [hfi'] at hfi''; cases hfi''; rw [hty'] at hty''; cases hty''
      subst hn
      have hC' := hC fl hcall (Or.inl ⟨vs, hvs⟩)
      rcases fl with w | ⟨_ | j, w⟩ | w | _ | t <;>
        simp only [Flow.retVals, Option.some.injEq, reduceCtorEq] at hvs <;> subst hvs <;>
        simp only [tailAnsS, ansFlow, Abstract.CallX.tailFlow, exitFlow, endOfFlowS,
          List.reverse_reverse, List.take_take, Nat.min_self, End.ret.injEq] at hend <;>
        obtain ⟨rfl, rfl⟩ := hend <;>
        rw [← List.take_take] <;>
        exact closeOk_vals hfi hty hC' rfl
    · have hC' := hC _ hlast (Or.inr trivial)
      simp only [tailAnsS, ansFlow, Abstract.CallX.tailFlow, exitFlow, endOfFlowS,
        End.ret.injEq] at hend
      obtain ⟨rfl, rfl⟩ := hend
      exact hC'
    · have hC' := hC _ hlast (Or.inr trivial)
      simp only [tailAnsS, End.ret.injEq] at hend
      obtain ⟨rfl, rfl⟩ := hend
      exact hC'
  · exact (hl _ (List.mem_singleton_self _)).elim

/-! ## The closure -/

/-- The property of closure behaviours proved by least-fixpoint induction. -/
def Good : (wasmHShapeS H).ClosedMod := fun g s a =>
  {y | y ∈ Shape.close wasmHOpenXPS g s a ∧ (∃ b s₂, y.2 = .ret b s₂) ∧
    ∀ b s₂, y = ([], .ret b s₂) → CloseOk closedCallXP (SCall.mk g a s b s₂)}

theorem mem_good {g : Nat} {s : Store H} {a : List Val}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} :
    y ∈ Good g s a ↔
      (y ∈ Shape.close wasmHOpenXPS g s a ∧ (∃ b s₂, y.2 = .ret b s₂) ∧
      ∀ b s₂, y = ([], .ret b s₂) → CloseOk closedCallXP (SCall.mk g a s b s₂)) :=
  Iff.rfl

/-- **Every behaviour of the session closure ends in `.ret`, and with the empty log it is a
`closedCallXP` answer.** -/
theorem close_le_good : Shape.close (wasmHOpenXPS (H := H)) ≤ Good := by
  refine OrderHom.lfp_le _ ?_
  intro g s a y hy
  obtain ⟨x, hx, hs⟩ := hy
  refine mem_good.mpr ⟨?_, ?_, ?_⟩
  · rw [← Shape.resolve_close]
    exact ⟨x, hx, hs.mono fun _ _ _ _ h => (mem_good.mp h).1⟩
  · exact subst_ret (fun _ _ _ _ h => (mem_good.mp h).2.1) hs (open_ret hx)
  · intro b s₂ hy
    obtain ⟨hend, hcalls⟩ := subst_nil hs b s₂ hy
    refine open_closeOk hx hend fun z hz => ?_
    obtain ⟨g', a', s', b', s'', rfl, hz'⟩ := hcalls z hz
    exact (mem_good.mp hz').2.2 b' s'' rfl

theorem close_good {g : Nat} {s : Store H} {a : List Val}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (h : y ∈ Shape.close wasmHOpenXPS g s a) : y ∈ Good g s a :=
  Pi.le_def.mp (Pi.le_def.mp (Pi.le_def.mp close_le_good g) s) a h

theorem closeOk_of_session {s s₂ : Store H} {g : Nat} {args : List Val}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} (h : ([], .ret b s₂) ∈ wasmEvFunXPS s (g, args)) :
    CloseOk closedCallXP (SCall.mk g args s b s₂) :=
  (mem_good.mp (close_good h)).2.2 b s₂ rfl

theorem session_ret {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHShapeS H).E (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (h : y ∈ wasmEvFunXPS s p) : ∃ b s₂, y.2 = .ret b s₂ :=
  (mem_good.mp (close_good h)).2.1

/-! ## Fitting answers -/

theorem closeOk_fit {C : Abstract.CallRel H} {g : Nat} {args : List Val} {s₁ s₂ : Store H}
    {b : (List Val ⊕ Nat) ⊕ PUnit.{1}} (h : CloseOk C (SCall.mk g args s₁ b s₂))
    (hf : ArgsFit s₁ g args) : CloseOk (fitP C) (SCall.mk g args s₁ b s₂) := by
  rcases b with (ws | t) | u
  · obtain ⟨fi, ps, rs, fl, vs, hfi, hty, hC, hvs, hws⟩ := h
    exact ⟨fi, ps, rs, fl, vs, hfi, hty, ⟨hC, hf⟩, hvs, hws⟩
  · exact ⟨h, hf⟩
  · exact ⟨h, hf⟩

/-! ## The logged machine runs host-free session behaviours -/

theorem chk_some {x : Option (Option Nat)} {n : Nat} (h : Interp.endsAt x n = true) :
    ∃ oc, x = some oc := by
  cases x with
  | none => simp [Interp.endsAt] at h
  | some oc => exact ⟨oc, rfl⟩

theorem body_chk {Γ : Ctx H} {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} (hg : Γ.Good s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : vs.length = ps.length) :
    Interp.endsAt (Interp.chkE (Interp.ehExt Γ.tags) Γ.funcs
      (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs.length [rs.length] (some 0)
      (liftInstrs fn.body)) rs.length = true := by
  have h := Γ.storeChk a fi fn ps rs (hg.1 ▸ hfi) hcode hty
  simpa [Frame.forCall, hvs] using h

/-- **A host-free session behaviour of a Wasm function is a logged machine run of its body**, with
every logged call answered by the fitting closure. -/
theorem logged_of_session {Γ : Ctx H} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} (hg : Γ.Good s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : vs.length = ps.length)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    (∃ (l : List (SCall H)) (st : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      (∀ c ∈ l, CloseOk (fitP closedCallXP) c) ∧ st.node.IsSink ∧
      EndRel st (s', f₂, .flow bfl) ∧ exitFlow rs.length bfl = some fl ∧
      e = endOfFlowS fl s') ∨
    (∃ (l l' : List (SCall H)) (st : MState H) (s₁ s₂ : Store H) (f₁ : Frame) (a' n : Nat)
      (args : List Val) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}),
      MRunL fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals)) l st ∧
      TailL fn.body st l' (s₁, f₁, .tail a' args n) ∧
      (∀ c ∈ l ++ l', CloseOk (fitP closedCallXP) c) ∧
      CloseOk (fitP closedCallXP) (SCall.mk a' args s₁ b s₂) ∧
      e = tailAnsS rs.length n b s₂) := by
  set f := Frame.forCall fi.module vs fn.locals
  have hchk := body_chk hg hfi hcode hty hvs
  obtain ⟨oc, hoc⟩ := chk_some hchk
  have hoc' : Interp.chkE (Interp.ehExt Γ.tags) s.funcs f.module f.locals.length rs.length
      [rs.length] (some ([] : List Val).length) (liftInstrs fn.body) = some oc := by
    rw [hg.1]; exact hoc
  -- the fitting logged run of a closed run of the body
  have hfit : ∀ r, EvalOXP closedCallXP s f [] (liftInstrs fn.body) r →
      ∃ l', EvalLXPS s f [] (liftInstrs fn.body) l' r ∧
        ∀ c ∈ l', CloseOk (fitP closedCallXP) c := fun r hr =>
    closed_iff_logged.mp
      ((Abstract.TypedCatFit.evalOXP_closed_iff_fit hg hoc' r).mp hr)
  obtain ⟨b₀, s₀, rfl⟩ : ∃ b s₂, e = .ret b s₂ := session_ret h
  have h' := h
  change _ ∈ Shape.close wasmHOpenXPS a s vs at h'
  rw [← Shape.resolve_close] at h'
  obtain ⟨x, hx, hs⟩ := h'
  obtain ⟨hend, hcalls⟩ := subst_nil hs b₀ s₀ rfl
  have hl : ∀ z ∈ x.1, CloseOk closedCallXP z := fun z hz => by
    obtain ⟨g', a', s', b', s'', rfl, hz'⟩ := hcalls z hz
    exact closeOk_of_session hz'
  rcases hx with
    ⟨fi₁, fn₁, ps₁, rs₁, s', f₂, bfl, fl, l, hfi₁, hcode₁, hty₁, hrun, hex, rfl⟩ |
    ⟨fi₁, fn₁, ps₁, rs₁, s₁, s₂, f₂, a', n, args, b, l, hfi₁, hcode₁, hty₁, hrun, rfl⟩ |
    ⟨fi₁, hh, ps₁, rs₁, s', r, fl, hfi₁, hcode₁, hty₁, hex, rfl⟩
  · rw [hfi] at hfi₁; cases hfi₁; rw [hcode] at hcode₁; cases hcode₁
    rw [hty] at hty₁; cases hty₁
    obtain ⟨l', hrun', hl'⟩ := hfit _ (closed_iff_logged.mpr ⟨l, hrun, hl⟩)
    have hnb : ∀ k ws, (POut.flow bfl) ≠ .flow (.brk (k + 1) ws) := by
      intro k ws hk; cases hk; simp [exitFlow] at hex
    obtain ⟨st, l₁, l₂, hm, rfl, hend'⟩ := backward hrun' hnb
    rcases hend' with ⟨hsink, rfl, hER⟩ | ht
    · refine .inl ⟨l₁, st, s', f₂, bfl, fl, hm, ?_, hsink, hER, hex, hend.symm⟩
      simpa using hl'
    · cases ht
  · rw [hfi] at hfi₁; cases hfi₁; rw [hcode] at hcode₁; cases hcode₁
    rw [hty] at hty₁; cases hty₁
    have hl₁ : ∀ z ∈ l, CloseOk closedCallXP z := fun z hz => hl z (List.mem_append_left _ hz)
    have hlast : CloseOk closedCallXP (SCall.mk a' args s₁ b s₂) :=
      hl _ (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨l', hrun', hl'⟩ := hfit _ (closed_iff_logged.mpr ⟨l, hrun, hl₁⟩)
    obtain ⟨st, l₁, l₂, hm, rfl, hend'⟩ := backward hrun' (fun _ _ h => by cases h)
    rcases hend' with ⟨hsink, -, hER⟩ | ht
    · exfalso
      unfold EndRel at hER
      split at hER
      · obtain ⟨_, h, -⟩ := hER; cases h
      · cases hER
      · obtain ⟨_, -, h⟩ := hER; cases h
      · exact hER
    · obtain ⟨fi', ps', rs', hfi', hty', hlen, -⟩ :=
        tail_fit_initialK (arityResp_fitClosed Γ) hg hchk hm ht hl'
      have hf : ArgsFit s₁ a' args := by
        intro fi'' ps'' rs'' hfi'' hty''
        rw [hfi'] at hfi''; cases hfi''; rw [hty'] at hty''; cases hty''
        exact hlen
      exact .inr ⟨l₁, l₂, st, s₁, s₂, f₂, a', n, args, b, hm, ht, hl',
        closeOk_fit hlast hf, hend.symm⟩
  · exact (hl _ (List.mem_singleton_self _)).elim

/-- **A host-free session behaviour of a Wasm function is an `MStepC` run of its body from the CFG
entry**, by `logged_of_session`, then `proj_initialK` or `proj_tail_initialK`. -/
theorem proj_of_session {P : Numerics.Profile} {host : HostSemantics H} {Γ : Ctx H}
    {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hg : Γ.Good s) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : vs.length = ps.length)
    (h : ([], e) ∈ wasmEvFunXPS s (a, vs)) :
    (∃ (st stC : MState H) (s' : Store H) (f₂ : Frame) (bfl fl : Flow),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) stC ∧
      ProjRel st stC ∧ st.node.IsSink ∧ EndRel st (s', f₂, .flow bfl) ∧
      exitFlow rs.length bfl = some fl ∧ e = endOfFlowS fl s') ∨
    (∃ (s₂ : Store H) (f₁ : Frame) (n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}),
      Relation.ReflTransGen (MStepC P host (fitP closedCallXP) fn.body)
        (initial fn.body s (Frame.forCall fi.module vs fn.locals)) (tailSink b s₂ f₁) ∧
      e = tailAnsS rs.length n b s₂) := by
  have hchk := body_chk hg hfi hcode hty hvs
  rcases logged_of_session hg hfi hcode hty hvs h with
    ⟨l, st, s', f₂, bfl, fl, hm, hl, hsink, hER, hex, rfl⟩ |
    ⟨l, l', st, s₁, s₂, f₁, a', n, args, b, hm, ht, hl, he, rfl⟩
  · obtain ⟨stC, hC, hR⟩ :=
      proj_initialK (P := P) (host := host) (arityResp_fitClosed Γ) hg hchk hm hl
    exact .inl ⟨st, stC, s', f₂, bfl, fl, hC, hR, hsink, hER, hex, rfl⟩
  · exact .inr ⟨s₂, f₁, n, b,
      proj_tail_initialK (P := P) (host := host) (arityResp_fitClosed Γ) hg hchk hm ht hl he,
      rfl⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLClose
