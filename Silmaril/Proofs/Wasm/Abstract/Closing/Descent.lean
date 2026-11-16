module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Proofs.Wasm.Abstract.Closing.Basic
public import Silmaril.Proofs.Wasm.Abstract.Closing.Core

/-!
# Infinite internal-call chains have no closed outcome: proofs

Let `g` be an infinite internal-call chain of `wasmOpen` (`Shape.Descends`
at every step, answers resolved by `Shape.close wasmOpen`). Then no function
call in the chain has a derivation of the recursive semantics `Eval`.

The proof is by induction on the derivation. A logged run of the same code
reaches the next call of the chain after a prefix of calls that all return
as the closure says. The closure is the recursive semantics, and `Eval` is
deterministic, so up to that call the logged run and the derivation agree.
At the call itself the derivation contains a derivation of the callee's body,
and the callee is the next element of the chain. That sub-derivation starts
the same situation again, one step further along the chain.

So `closeD wasmOpen` is sound for Core 3.0: under the Core hypotheses,
everything it gives is a Core behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Closing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## Determinism -/

theorem eval_det {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r₁ r₂ : Store H × Frame × Flow} (h₁ : Eval s f stk es r₁) (h₂ : Eval s f stk es r₂) :
    r₁ = r₂ := by
  obtain ⟨n₁, e₁⟩ := run_of_eval h₁
  obtain ⟨n₂, e₂⟩ := run_of_eval h₂
  have := (run_mono (Nat.le_max_left n₁ n₂) e₁).symm.trans (run_mono (Nat.le_max_right n₁ n₂) e₂)
  exact Option.some.inj this

/-- A logged run whose calls all return as the closure says agrees with any
derivation of the recursive semantics. -/
theorem agree {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (OCall H)}
    {r₁ r₂ : Store H × Frame × Flow} (hL : EvalL s f stk es l r₁) (hl : AllRet (toClosed closedCall) l)
    (hE : Eval s f stk es r₂) : r₁ = r₂ :=
  eval_det (evalO_closed_iff.mp ((evalO_of_evalL hL).1 hl)) hE

/-- A call answered by returned values in the closure: the callee's
derivation returns those values, in that store. -/
theorem callee_ret {a : Nat} {args : List Val} {s₁ s₂ s₂' : Store H} {ws : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame} {fl : Flow}
    (h : Ret (toClosed closedCall) (OCall.mk a args s₁ (.inl ws) s₂))
    (hfi : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hE : Eval s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (s₂', f₂, fl)) :
    s₂' = s₂ ∧ ∃ vs, fl.retVals = some vs ∧ ws.reverse = vs.take rs.length := by
  obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl (C := closedCall) h hfi hty
  rw [closedCall_eq] at hC
  obtain ⟨fi', fn', ps', rs', f₂', hfi', hcode', -, hE'⟩ := hC
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain rfl : fn = fn' := FuncCode.wasm.inj (hcode.symm.trans hcode')
  have he := eval_det hE hE'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  exact ⟨rfl, vs, hvs, hws⟩

theorem escapes_blockVals {fl : Flow} {vs : List Val} (h : fl.Escapes) (h' : fl.blockVals = some vs) :
    False := by
  rcases fl with _ | ⟨_ | _, _⟩ | _ | _ | _ <;> simp_all [Flow.Escapes, Flow.blockVals]

/-! ## Reaching the next call of a chain -/

section Chain

variable (g : Nat → (wasmOShape H).self.Op)

/-- The log `l` reaches the call `g (k + 1)`, every call before it returning
as the closure says. -/
def Hit (k : Nat) (l : List (OCall H)) : Prop :=
  ∃ u z rest, z.1 = .inr (g (k + 1)) ∧ l = u ++ z :: rest ∧ AllRet (toClosed closedCall) u

variable {g}

theorem hit_nil {k : Nat} : ¬ Hit g k [] := by
  rintro ⟨u, z, rest, -, h, -⟩
  simp at h

theorem hit_cons {k : Nat} {z₀ : OCall H} {l : List (OCall H)} (h : Hit g k (z₀ :: l)) :
    z₀.1 = .inr (g (k + 1)) ∨ (Ret (toClosed closedCall) z₀ ∧ Hit g k l) := by
  obtain ⟨u, z, rest, hz, hl, hu⟩ := h
  rcases u with _ | ⟨w, u⟩
  · obtain ⟨rfl, -⟩ := List.cons.inj hl
    exact .inl hz
  · obtain ⟨rfl, hl'⟩ := List.cons.inj hl
    rw [allRet_cons] at hu
    exact .inr ⟨hu.1, u, z, rest, hz, hl', hu.2⟩

theorem hit_append {k : Nat} {l₁ l₂ : List (OCall H)} (h : Hit g k (l₁ ++ l₂)) :
    Hit g k l₁ ∨ (AllRet (toClosed closedCall) l₁ ∧ Hit g k l₂) := by
  induction l₁ with
  | nil => exact .inr ⟨allRet_nil _, h⟩
  | cons z₀ l₁ ih =>
    rcases hit_cons h with hz | ⟨hz, h⟩
    · exact .inl ⟨[], z₀, l₁, hz, rfl, allRet_nil _⟩
    · rcases ih h with ⟨u, z, rest, hz', rfl, hu⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨z₀ :: u, z, rest, hz', rfl, allRet_cons.2 ⟨hz, hu⟩⟩
      · exact .inr ⟨allRet_cons.2 ⟨hz, h₁⟩, h₂⟩

/-- The log of a call: the args part, the call, the continuation. -/
theorem hit_call {k : Nat} {l₁ l₂ : List (OCall H)} {z₀ : OCall H} (h : Hit g k (l₁ ++ z₀ :: l₂)) :
    Hit g k l₁ ∨ (AllRet (toClosed closedCall) l₁ ∧ z₀.1 = .inr (g (k + 1))) ∨
      (AllRet (toClosed closedCall) l₁ ∧ Ret (toClosed closedCall) z₀ ∧ Hit g k l₂) := by
  rcases hit_append h with h | ⟨h₁, h⟩
  · exact .inl h
  · rcases hit_cons h with h | ⟨h₂, h⟩
    · exact .inr (.inl ⟨h₁, h⟩)
    · exact .inr (.inr ⟨h₁, h₂, h⟩)

theorem allRet_of_substPre {c : (wasmOShape H).ClosedMod} {u : List (OCall H)}
    {q : List (Call Sig.empty)} (h : Shape.SubstPre c u q) : AllRet c u := by
  induction h with
  | nil => exact allRet_nil c
  | @ext m => exact PEmpty.elim m
  | @int g' a s b s' rest c₁ q hc _ ih =>
    exact allRet_cons.2 ⟨⟨g', a, s, b, s', rfl, by obtain rfl := nil_of_empty c₁; exact hc⟩, ih⟩

theorem call_target {a : Nat} {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat} {k : Nat}
    (h : (OCall.mk a args s₁ b s₂).1 = .inr (g (k + 1))) : g (k + 1) = ⟨a, (args, s₁)⟩ :=
  (Sum.inr.inj h).symm

variable (hD : ∀ n, Shape.Descends wasmOpen (Shape.close wasmOpen) (g n) [] (g (n + 1)))
include hD

/-- At the call `g (k + 1)` itself: the callee's body, by the chain, reaches
`g (k + 2)`. -/
theorem self_step {s₁ : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {args : List Val}
    {k : Nat} (hfi : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hg : g (k + 1) = ⟨a, (args, s₁)⟩)
    (ih : ∀ {l : List (OCall H)} {r' : Store H × Frame × Flow},
      EvalL s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) l r' →
        ∀ k, Hit g k l → False) : False := by
  obtain ⟨z, hz, u, ans, rest, hzl, hsub⟩ := hD (k + 1)
  rw [hg] at hz
  obtain ⟨fi', fn', _, _, _, _, _, _, hfi', hcode', _, hEL, _, _⟩ := hz
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain rfl : fn = fn' := FuncCode.wasm.inj (hcode.symm.trans hcode')
  have hu := allRet_of_substPre hsub
  rw [close_eq] at hu
  exact ih hEL (k + 1) ⟨u, ⟨.inr (g (k + 1 + 1)), ans⟩, rest, rfl, hzl, hu⟩

/-- **No derivation runs code whose logged run reaches the chain.** -/
theorem no_eval_of_hit {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (D : Eval s f stk es r) :
    ∀ {l : List (OCall H)} {r' : Store H × Frame × Flow}, EvalL s f stk es l r' →
      ∀ k, Hit g k l → False := by
  induction D with
  | nil => intro l r' hL k h₀; cases hL; exact hit_nil h₀
  | argsAbort hargs hfl ih =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ih hargs' k h₀
    | callRet hargs' _ _ _ =>
      rcases hit_call h₀ with h | ⟨h₁, -⟩ | ⟨h₁, -, -⟩
      · exact ih hargs' k h
      all_goals cases agree hargs' h₁ hargs; exact hfl trivial
    | callThrow hargs' _ _ =>
      rcases hit_call h₀ with h | ⟨h₁, -⟩ | ⟨-, -, h⟩
      · exact ih hargs' k h
      · cases agree hargs' h₁ hargs; exact hfl trivial
      · exact hit_nil h
    | opOk _ hargs' _ _ =>
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ih hargs' k h
      · cases agree hargs' h₁ hargs; exact hfl trivial
    | opStop _ hargs' _ _ => exact ih hargs' k h₀
  | callOk hargs hfi hcode hty hbody hvs hk ihA ihB ihK =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ihA hargs' k h₀
    | callRet hargs' hfi' hty' hk' =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨h₁, hz, h⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        obtain ⟨rfl, vs', hvs', hws⟩ := callee_ret hz (funcs_of_func? hfi) hcode hty hbody
        obtain rfl : vs' = _ := Option.some.inj (hvs'.symm.trans hvs)
        rw [hws] at hk'
        exact ihK hk' k h
    | callThrow hargs' hfi' hty' =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨-, -, h⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · exact hit_nil h
    | opOk hi => exact absurd rfl (hi _)
    | opStop hi => exact absurd rfl (hi _)
  | callTrap hargs hfi hcode hty hbody ihA ihB =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ihA hargs' k h₀
    | callRet hargs' hfi' hty' _ =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨h₁, hz, -⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        obtain ⟨-, vs', hvs', -⟩ := callee_ret hz (funcs_of_func? hfi) hcode hty hbody
        cases hvs'
    | callThrow hargs' hfi' hty' =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨-, -, h⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · exact hit_nil h
    | opOk hi => exact absurd rfl (hi _)
    | opStop hi => exact absurd rfl (hi _)
  | callThrow hargs hfi hcode hty hbody ihA ihB =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ihA hargs' k h₀
    | callRet hargs' hfi' hty' _ =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨h₁, hz, -⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        obtain ⟨-, vs', hvs', -⟩ := callee_ret hz (funcs_of_func? hfi) hcode hty hbody
        cases hvs'
    | callThrow hargs' hfi' hty' =>
      rcases hit_call h₀ with h | ⟨h₁, hz⟩ | ⟨-, -, h⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hfi'.symm.trans hfi))
        obtain ⟨⟨⟩, ⟨⟩⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        exact self_step hD (funcs_of_func? hfi) hcode (call_target hz) ihB
      · exact hit_nil h
    | opOk hi => exact absurd rfl (hi _)
    | opStop hi => exact absurd rfl (hi _)
  | opOk hi hargs hflat hk ihA ihK =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ihA hargs' k h₀
    | callRet => exact absurd rfl (hi _)
    | callThrow => exact absurd rfl (hi _)
    | opOk _ hargs' hflat' hk' =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        cases Option.some.inj (hflat'.symm.trans hflat)
        exact ihK hk' k h
    | opStop _ hargs' _ _ => exact ihA hargs' k h₀
  | opStop hi hargs hflat hfl ihA =>
    intro l r' hL k h₀
    cases hL with
    | argsAbort hargs' _ => exact ihA hargs' k h₀
    | callRet => exact absurd rfl (hi _)
    | callThrow => exact absurd rfl (hi _)
    | opOk _ hargs' hflat' _ =>
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihA hargs' k h
      · cases agree hargs' h₁ hargs
        cases Option.some.inj (hflat'.symm.trans hflat)
        exact hfl trivial
    | opStop _ hargs' _ _ => exact ihA hargs' k h₀
  | blockOk har hbody hvs hk ihB ihK =>
    intro l r' hL k h₀
    cases hL with
    | blockOk har' hbody' hvs' hk' =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        cases Option.some.inj (hvs'.symm.trans hvs)
        exact ihK hk' k h
    | blockBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | blockEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | blockBrk har hbody ihB =>
    intro l r' hL k h₀
    cases hL with
    | blockOk har' hbody' hvs' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        cases hvs'
    | blockBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | blockEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | blockEsc har hbody hfl ihB =>
    intro l r' hL k h₀
    cases hL with
    | blockOk har' hbody' hvs' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        exact escapes_blockVals hfl hvs'
    | blockBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | blockEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | loopOk har hbody hk ihB ihK =>
    intro l r' hL k h₀
    cases hL with
    | loopOk har' hbody' hk' =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        exact ihK hk' k h
    | loopBack har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
    | loopBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | loopEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | loopBack har hbody hk ihB ihK =>
    intro l r' hL k h₀
    cases hL with
    | loopOk har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
    | loopBack har' hbody' hk' =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        exact ihK hk' k h
    | loopBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | loopEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | loopBrk har hbody ihB =>
    intro l r' hL k h₀
    cases hL with
    | loopOk har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
    | loopBack har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
    | loopBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | loopEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | loopEsc har hbody hfl ihB =>
    intro l r' hL k h₀
    cases hL with
    | loopOk har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        exact hfl
    | loopBack har' hbody' _ =>
      cases Option.some.inj (har'.symm.trans har)
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihB hbody' k h
      · cases agree hbody' h₁ hbody
        exact hfl
    | loopBrk har' hbody' => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
    | loopEsc har' hbody' _ => cases Option.some.inj (har'.symm.trans har); exact ihB hbody' k h₀
  | ifOk hc hb har harm hvs hk ihC ihA ihK =>
    intro l r' hL k h₀
    cases hL with
    | ifOk hc' hb' har' harm' hvs' hk' =>
      rcases hit_append h₀ with h | ⟨h₁₂, h⟩
      · rcases hit_append h with h | ⟨h₁, h⟩
        · exact ihC hc' k h
        · cases agree hc' h₁ hc
          cases Option.some.inj (hb'.symm.trans hb)
          cases Option.some.inj (har'.symm.trans har)
          exact ihA harm' k h
      · obtain ⟨h₁, h₂⟩ := allRet_append.1 h₁₂
        cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        cases agree harm' h₂ harm
        cases Option.some.inj (hvs'.symm.trans hvs)
        exact ihK hk' k h
    | ifBrk hc' hb' har' harm' =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifEsc hc' hb' har' harm' _ =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifAbort hc' _ => exact ihC hc' k h₀
  | ifBrk hc hb har harm ihC ihA =>
    intro l r' hL k h₀
    cases hL with
    | ifOk hc' hb' har' harm' hvs' _ =>
      rcases hit_append h₀ with h | ⟨h₁₂, -⟩
      · rcases hit_append h with h | ⟨h₁, h⟩
        · exact ihC hc' k h
        · cases agree hc' h₁ hc
          cases Option.some.inj (hb'.symm.trans hb)
          cases Option.some.inj (har'.symm.trans har)
          exact ihA harm' k h
      · obtain ⟨h₁, h₂⟩ := allRet_append.1 h₁₂
        cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        cases agree harm' h₂ harm
        cases hvs'
    | ifBrk hc' hb' har' harm' =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifEsc hc' hb' har' harm' _ =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifAbort hc' _ => exact ihC hc' k h₀
  | ifEsc hc hb har harm hfl ihC ihA =>
    intro l r' hL k h₀
    cases hL with
    | ifOk hc' hb' har' harm' hvs' _ =>
      rcases hit_append h₀ with h | ⟨h₁₂, -⟩
      · rcases hit_append h with h | ⟨h₁, h⟩
        · exact ihC hc' k h
        · cases agree hc' h₁ hc
          cases Option.some.inj (hb'.symm.trans hb)
          cases Option.some.inj (har'.symm.trans har)
          exact ihA harm' k h
      · obtain ⟨h₁, h₂⟩ := allRet_append.1 h₁₂
        cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        cases agree harm' h₂ harm
        exact escapes_blockVals hfl hvs'
    | ifBrk hc' hb' har' harm' =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifEsc hc' hb' har' harm' _ =>
      rcases hit_append h₀ with h | ⟨h₁, h⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc
        cases Option.some.inj (hb'.symm.trans hb)
        cases Option.some.inj (har'.symm.trans har)
        exact ihA harm' k h
    | ifAbort hc' _ => exact ihC hc' k h₀
  | ifAbort hc hfl ihC =>
    intro l r' hL k h₀
    cases hL with
    | ifOk hc' _ _ _ _ _ =>
      rcases hit_append h₀ with h | ⟨h₁₂, -⟩
      · rcases hit_append h with h | ⟨h₁, -⟩
        · exact ihC hc' k h
        · cases agree hc' h₁ hc; exact hfl trivial
      · cases agree hc' (allRet_append.1 h₁₂).1 hc; exact hfl trivial
    | ifBrk hc' _ _ _ =>
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc; exact hfl trivial
    | ifEsc hc' _ _ _ _ =>
      rcases hit_append h₀ with h | ⟨h₁, -⟩
      · exact ihC hc' k h
      · cases agree hc' h₁ hc; exact hfl trivial
    | ifAbort hc' _ => exact ihC hc' k h₀

/-- **The start of an infinite internal-call chain has no closed outcome.** -/
theorem no_closedOutcome_of_chain {s' : Store H} {fl : Flow} :
    ¬ ClosedOutcome (g 0).2.2 (g 0).1 (g 0).2.1 s' fl := by
  rintro ⟨fi, fn, _, _, _, _, hfi, hcode, _, hE, _⟩
  obtain ⟨z, hz, u, ans, rest, hzl, hsub⟩ := hD 0
  obtain ⟨fi', fn', _, _, _, _, _, _, hfi', hcode', _, hEL, _, _⟩ := hz
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain rfl : fn = fn' := FuncCode.wasm.inj (hcode.symm.trans hcode')
  have hu := allRet_of_substPre hsub
  rw [close_eq] at hu
  exact no_eval_of_hit hD (evalO_closed_iff.mp hE) hEL 0 ⟨u, ⟨.inr (g (0 + 1)), ans⟩, rest, rfl, hzl, hu⟩

end Chain

/-- A divergence chain from a call rules out closed outcomes of it. -/
theorem no_closedOutcome_of_divChain {s : Store H} {a : Nat} {vs : List Val}
    {qs : List (Call Sig.empty)}
    (h : Shape.DivChain wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ qs) (s' : Store H) (fl : Flow) :
    ¬ ClosedOutcome s a vs s' fl := by
  obtain ⟨g, q, -, hg, hD, -, -⟩ := h
  have hq : ∀ n, q n = [] := fun n => nil_of_empty _
  have hD' : ∀ n, Shape.Descends wasmOpen (Shape.close wasmOpen) (g n) [] (g (n + 1)) := fun n => by
    rw [← hq n]; exact hD n
  have := no_closedOutcome_of_chain hD' (s' := s') (fl := fl)
  rwa [hg] at this

/-- **`closeD` is sound for Core 3.0**: under the Core hypotheses, every
behaviour it gives is in `wasmFun`. -/
theorem closeD_subset_wasmFun {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Shape.closeD wasmOpen a s vs ⊆ wasmFun P closedHost a s vs := by
  rw [wasmFun_eq_close hs hF hS hok P]
  rintro ⟨q, e⟩ (h | ⟨rfl, hc⟩)
  · exact .inl h
  · refine .inr ⟨by rw [nil_of_empty q], ?_⟩
    rw [close_wasmOpen, Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨s', fl, hco, -⟩
    exact no_closedOutcome_of_divChain hc s' fl hco

end Silmaril.Proofs.Wasm.Abstract.Closing
