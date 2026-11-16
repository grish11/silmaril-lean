module

public import Silmaril.Proofs.Wasm.Abstract.Decomp.Native
public import Silmaril.Proofs.Wasm.Abstract.Closing.Descent

/-!
# Native descents are `Shape.Descends` of the open module (proofs)

`BodyReach x y` (native: the body of `x` reaches the call `y` after a
terminating prefix) is `Shape.Descends wasmOpen (Shape.close wasmOpen) x [] y`
(`bodyReach_iff_descends`), when `x` has a function type.

* `reach_log`: a reach gives a logged run that reaches the call, every call
  before it answered as the closure says. The call itself takes the exception
  answer, so the run stops there.
* `reach_of_log`: such a logged run gives a reach; the prefix evaluates
  because the closure is the recursive semantics.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Decomp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Proofs.Wasm.Abstract.Closing

variable {H : Type}

/-- The log reaches the call `y`, every call before it returning. -/
abbrev HitY (y : (wasmOShape H).self.Op) (l : List (OCall H)) : Prop := Hit (fun _ => y) 0 l

theorem hitY_prefix {y : (wasmOShape H).self.Op} {u l : List (OCall H)}
    (hu : AllRet (toClosed closedCall) u) (h : HitY y l) : HitY y (u ++ l) := by
  obtain ⟨u', z, rest, hz, rfl, hu'⟩ := h
  exact ⟨u ++ u', z, rest, hz, by simp, allRet_append.2 ⟨hu, hu'⟩⟩

theorem evalL_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) (hr : r.2.2 ≠ .trap) :
    ∃ l, EvalL s f stk es l r ∧ AllRet (toClosed closedCall) l := by
  have d := (evalO_closed_iff.mpr h).mono closedCall_le_ofClosed
  obtain ⟨l, r', dL, hm⟩ := evalL_of_evalO d
  obtain ⟨hl, rfl⟩ := hm.normal hr
  rw [close_eq] at hl
  exact ⟨l, dL, hl⟩

theorem eval_of_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (h : EvalL s f stk es l r)
    (hl : AllRet (toClosed closedCall) l) : Eval s f stk es r :=
  evalO_closed_iff.mp ((evalO_of_evalL h).1 hl)

theorem ret_of_eval {s₁ s₂ : Store H} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {f₂ : Frame} {fl : Flow} {vs : List Val} {args : List Val}
    (hfi : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Eval s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl))
    (hvs : fl.retVals = some vs) :
    Ret (toClosed closedCall) (OCall.mk a args s₁ (.inl (vs.take rs.length).reverse) s₂) := by
  have hC : (closedCall : CallRel H) s₁ a args (s₂, fl) := by
    rw [closedCall_eq]
    exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, hbody⟩
  have := ret_ofClosed_inl (closedCall_le_ofClosed _ _ _ _ hC) hfi hty hvs
  rwa [close_eq] at this

theorem ne_trap_of_blockVals {fl : Flow} {vs : List Val} (h : fl.blockVals = some vs) :
    fl ≠ .trap := by
  rintro rfl
  simp [Flow.blockVals] at h

/-- **A reach is a logged run reaching the call.** -/
theorem reach_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : Reach s f stk es y) :
    ∃ l s' f' t, EvalL s f stk es l (s', f', .throw t) ∧ HitY y l := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hargs nofun
    exact ⟨_, s₁, f₁, 0, EvalL.callThrow (t := 0) (s₂ := s₁) d₁ hfi hty, ⟨l₁, _, [], rfl, rfl, h₁⟩⟩
  | args _ ih =>
    obtain ⟨l, s', f', t, d, h⟩ := ih
    exact ⟨l, s', f', t, .argsAbort d Flow.notNormal_throw, h⟩
  | @callK s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl y hargs hfi hcode hty hbody hvs _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hargs nofun
    have hz := ret_of_eval (funcs_of_func? hfi) hcode hty hbody hvs
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    refine ⟨_, s', f', t, EvalL.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂), ?_⟩
    have := hitY_prefix (allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil _⟩⟩) h₂
    simpa using this
  | opK hi hargs hflat _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hargs nofun
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    exact ⟨_, s', f', t, .opOk hi d₁ hflat d₂, hitY_prefix h₁ h₂⟩
  | block har _ ih =>
    obtain ⟨l, s', f', t, d, h⟩ := ih
    exact ⟨l, s', f', t, .blockEsc har d trivial, h⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hbody (ne_trap_of_blockVals hvs)
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    exact ⟨_, s', f', t, .blockOk har d₁ hvs d₂, hitY_prefix h₁ h₂⟩
  | loop har _ ih =>
    obtain ⟨l, s', f', t, d, h⟩ := ih
    exact ⟨l, s', f', t, .loopEsc har d trivial, h⟩
  | loopK har hbody _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hbody nofun
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    exact ⟨_, s', f', t, .loopOk har d₁ d₂, hitY_prefix h₁ h₂⟩
  | loopBack har hbody _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hbody nofun
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    exact ⟨_, s', f', t, .loopBack har d₁ d₂, hitY_prefix h₁ h₂⟩
  | cond _ ih =>
    obtain ⟨l, s', f', t, d, h⟩ := ih
    exact ⟨l, s', f', t, .ifAbort d Flow.notNormal_throw, h⟩
  | arm hc hb har _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hc nofun
    obtain ⟨l₂, s', f', t, d₂, h₂⟩ := ih
    exact ⟨_, s', f', t, .ifEsc d₁ hb har d₂ trivial, hitY_prefix h₁ h₂⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨l₁, d₁, h₁⟩ := evalL_of_eval hc nofun
    obtain ⟨l₂, d₂, h₂⟩ := evalL_of_eval harm (ne_trap_of_blockVals hvs)
    obtain ⟨l₃, s', f', t, d₃, h₃⟩ := ih
    exact ⟨_, s', f', t, .ifOk d₁ hb har d₂ hvs d₃, hitY_prefix (allRet_append.2 ⟨h₁, h₂⟩) h₃⟩

/-- **A logged run reaching the call is a reach.** -/
theorem reach_of_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} {y : (wasmOShape H).self.Op}
    (d : EvalL s f stk es l r) (h : HitY y l) : Reach s f stk es y := by
  induction d with
  | nil => exact absurd h hit_nil
  | argsAbort _ _ ih => exact .args (ih h)
  | callRet d₁ hfi hty d₂ ih₁ ih₂ =>
    rcases hit_call h with h | ⟨h₁, hz⟩ | ⟨h₁, hz, h⟩
    · exact .args (ih₁ h)
    · rw [show y = _ from call_target (g := fun _ => y) (k := 0) hz]
      exact .here (eval_of_evalL d₁ h₁) hfi hty
    · obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl hz (funcs_of_func? hfi) hty
      rw [closedCall_eq] at hC
      obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hbody⟩ := hC
      obtain rfl : _ = fi' := Option.some.inj ((funcs_of_func? hfi).symm.trans hfi')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
      have hk := ih₂ h
      rw [hws] at hk
      exact .callK (eval_of_evalL d₁ h₁) hfi hcode hty hbody hvs hk
  | callThrow d₁ hfi hty ih₁ =>
    rcases hit_call h with h | ⟨h₁, hz⟩ | ⟨-, -, h⟩
    · exact .args (ih₁ h)
    · rw [show y = _ from call_target (g := fun _ => y) (k := 0) hz]
      exact .here (eval_of_evalL d₁ h₁) hfi hty
    · exact absurd h hit_nil
  | opOk hi d₁ hflat _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .args (ih₁ h)
    · exact .opK hi (eval_of_evalL d₁ h₁) hflat (ih₂ h)
  | opStop _ _ _ _ ih => exact .args (ih h)
  | blockOk har d₁ hvs _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .block har (ih₁ h)
    · exact .blockK har (eval_of_evalL d₁ h₁) hvs (ih₂ h)
  | blockBrk har _ ih => exact .block har (ih h)
  | blockEsc har _ _ ih => exact .block har (ih h)
  | loopOk har d₁ _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .loop har (ih₁ h)
    · exact .loopK har (eval_of_evalL d₁ h₁) (ih₂ h)
  | loopBack har d₁ _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .loop har (ih₁ h)
    · exact .loopBack har (eval_of_evalL d₁ h₁) (ih₂ h)
  | loopBrk har _ ih => exact .loop har (ih h)
  | loopEsc har _ _ ih => exact .loop har (ih h)
  | ifOk d₁ hb har d₂ hvs _ ih₁ ih₂ ih₃ =>
    rcases hit_append h with h | ⟨h₁₂, h⟩
    · rcases hit_append h with h | ⟨h₁, h⟩
      · exact .cond (ih₁ h)
      · exact .arm (eval_of_evalL d₁ h₁) hb har (ih₂ h)
    · obtain ⟨h₁, h₂⟩ := allRet_append.1 h₁₂
      exact .ifK (eval_of_evalL d₁ h₁) hb har (eval_of_evalL d₂ h₂) hvs (ih₃ h)
  | ifBrk d₁ hb har _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .cond (ih₁ h)
    · exact .arm (eval_of_evalL d₁ h₁) hb har (ih₂ h)
  | ifEsc d₁ hb har _ _ ih₁ ih₂ =>
    rcases hit_append h with h | ⟨h₁, h⟩
    · exact .cond (ih₁ h)
    · exact .arm (eval_of_evalL d₁ h₁) hb har (ih₂ h)
  | ifAbort _ _ ih => exact .cond (ih h)

theorem substPre_of_allRet {c : (wasmOShape H).ClosedMod} :
    ∀ {u : List (OCall H)}, AllRet c u → Shape.SubstPre c u []
  | [], _ => .nil
  | z :: u, h => by
    rw [allRet_cons] at h
    obtain ⟨⟨a, args, s₁, b, s₂, rfl, hz⟩, hu⟩ := h
    exact Shape.SubstPre.int (c₁ := []) hz (substPre_of_allRet hu)

/-- **Native descents are `Shape.Descends`** of the open module, from a call
with a function type. -/
theorem bodyReach_iff_descends {x y : (wasmOShape H).self.Op}
    (hx : ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), x.2.2.funcs[x.1]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)) :
    BodyReach x y ↔ Shape.Descends wasmOpen (Shape.close wasmOpen) x [] y := by
  constructor
  · rintro ⟨fi, fn, hfi, hcode, hr⟩
    obtain ⟨fi', ps, rs, hfi', hty⟩ := hx
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨l, s', f', t, d, u, ⟨zop, zans⟩, rest, hz, rfl, hu⟩ := reach_log hr
    obtain rfl : zop = .inr y := hz
    rw [← close_eq] at hu
    exact ⟨(u ++ ⟨.inr y, zans⟩ :: rest, endOfFlow (.throw t) s'),
      ⟨fi, fn, ps, rs, s', f', .throw t, .throw t, hfi, hcode, hty, d, rfl, rfl⟩,
      u, zans, rest, rfl, substPre_of_allRet hu⟩
  · rintro ⟨z, hzm, u, ans, rest, hzl, hsub⟩
    obtain ⟨fi, fn, _, _, _, _, _, _, hfi, hcode, _, hEL, _, _⟩ := hzm
    have hu := allRet_of_substPre hsub
    rw [close_eq] at hu
    exact ⟨fi, fn, hfi, hcode, reach_of_log hEL ⟨u, ⟨.inr y, ans⟩, rest, rfl, hzl, hu⟩⟩

end Silmaril.Proofs.Wasm.Abstract.Decomp
