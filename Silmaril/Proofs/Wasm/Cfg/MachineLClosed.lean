module

public import Silmaril.Proofs.Wasm.Cfg.MachineLPend
public import Silmaril.Wasm.Abstract.CallXP.Defs

@[expose] public section

/-!
# Closed runs as logged runs (H2 divergence support, proofs)

`MachineL.CloseOk C e` (defined in the header): the logged internal call `e` is an answer of the call relation `C`. Its values are
the callee's top `rs` results (`rs` the callee's result types), as `EvalOXP`'s `callOk` keeps them;
an exception or a trap is `C`'s, with the store `C` leaves. `closed_logged`, `logged_closed`: a run
of `EvalOXP C` is exactly an `EvalLXPS` run all of whose entries are `C`-answers.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLClosed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall CallRel)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Cfg.MachineL (CloseOk)

variable {H : Type}

/-- Every entry is a `C`-answer. -/
def AllOk (C : CallRel H) (l : List (SCall H)) : Prop := ∀ e ∈ l, CloseOk C e

theorem allOk_nil (C : CallRel H) : AllOk C ([] : List (SCall H)) := by simp [AllOk]

theorem allOk_append {C : CallRel H} {l₁ l₂ : List (SCall H)} :
    AllOk C (l₁ ++ l₂) ↔ AllOk C l₁ ∧ AllOk C l₂ := by
  simp only [AllOk, List.mem_append]; constructor
  · intro h; exact ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩
  · rintro ⟨h₁, h₂⟩ e (he | he); exacts [h₁ e he, h₂ e he]

theorem allOk_cons {C : CallRel H} {e : SCall H} {l : List (SCall H)} :
    AllOk C (e :: l) ↔ CloseOk C e ∧ AllOk C l := by
  simp [AllOk]

theorem func?_funcs {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : s.func? f x = some (a, fi)) : s.funcs[a]? = some fi := by
  simp only [Store.func?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a', -, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨fi', hfi, rfl, rfl⟩ := h
  exact hfi

theorem evalFlat_call {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} :
    evalFlat s f stk (.call x) = none := rfl

theorem not_call_of_flat {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    (h : evalFlat s f stk i = some (s', f', fl)) : ∀ x, i ≠ .call x := by
  rintro x rfl; simp [evalFlat_call] at h

/-- **Closed runs are logged runs answered by `C`.** -/
theorem closed_logged {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    ∃ l, EvalLXPS s f stk es l r ∧ AllOk C l := by
  induction h with
  | nil => exact ⟨[], .nil, allOk_nil C⟩
  | argsAbort _ ho ih => obtain ⟨l, h, hl⟩ := ih; exact ⟨l, .argsAbort h ho, hl⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    refine ⟨_, .callRet (ws := (_ : List Val).take _ |>.reverse) h₁ hfi hty (by simpa using h₂), ?_⟩
    refine allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨?_, hl₂⟩⟩
    exact ⟨_, _, _, _, _, func?_funcs hfi, hty, hcall, hvs, rfl⟩
  | callTrap _ hfi hty hcall iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha
    exact ⟨_, .callTrap h₁ hfi hty, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall, allOk_nil C⟩⟩⟩
  | callThrow _ hfi hty hcall iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha
    exact ⟨_, .callThrow h₁ hfi hty, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall, allOk_nil C⟩⟩⟩
  | opOk hi _ hflat _ iha ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    exact ⟨_, .opOk hi h₁ hflat h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | opStop hi _ hflat hfl iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha
    exact ⟨_, .opStop hi h₁ hflat hfl, hl₁⟩
  | blockOk har _ hvs _ ihb ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihb; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    exact ⟨_, .blockOk har h₁ hvs h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | blockBrk har _ ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .blockBrk har h₁, hl₁⟩
  | blockEsc har _ ho ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .blockEsc har h₁ ho, hl₁⟩
  | loopOk har _ _ ihb ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihb; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    exact ⟨_, .loopOk har h₁ h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | loopBack har _ _ ihb ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihb; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    exact ⟨_, .loopBack har h₁ h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | loopBrk har _ ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .loopBrk har h₁, hl₁⟩
  | loopEsc har _ ho ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .loopEsc har h₁ ho, hl₁⟩
  | ifOk _ hb har _ hvs _ ihc iha ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihc; obtain ⟨l₂, h₂, hl₂⟩ := iha; obtain ⟨l₃, h₃, hl₃⟩ := ihk
    exact ⟨_, .ifOk h₁ hb har h₂ hvs h₃, allOk_append.2 ⟨allOk_append.2 ⟨hl₁, hl₂⟩, hl₃⟩⟩
  | ifBrk _ hb har _ ihc iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihc; obtain ⟨l₂, h₂, hl₂⟩ := iha
    exact ⟨_, .ifBrk h₁ hb har h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | ifEsc _ hb har _ ho ihc iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihc; obtain ⟨l₂, h₂, hl₂⟩ := iha
    exact ⟨_, .ifEsc h₁ hb har h₂ ho, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | ifAbort _ ho ihc => obtain ⟨l₁, h₁, hl₁⟩ := ihc; exact ⟨_, .ifAbort h₁ ho, hl₁⟩
  | callIndOk _ hres hfi hty hy hcall hvs _ iha ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    refine ⟨_, .indRet (ws := (_ : List Val).take _ |>.reverse) h₁ hres hfi hty hy
      (by simpa using h₂), ?_⟩
    exact allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨⟨_, _, _, _, _, hfi, hty, hcall, hvs, rfl⟩, hl₂⟩⟩
  | callIndRes _ hres iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .indRes h₁ hres, hl₁⟩
  | @callIndStop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fl _ hres hfi hty hy hcall hfl iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha
    cases fl with
    | trap =>
      exact ⟨_, .indTrap h₁ hres hfi hty hy, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall,
        allOk_nil C⟩⟩⟩
    | throw t =>
      exact ⟨_, .indThrow h₁ hres hfi hty hy, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall,
        allOk_nil C⟩⟩⟩
    | _ => exact absurd hfl id
  | callRefOk _ hfi hty hy hcall hvs _ iha ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    refine ⟨_, .refRet (ws := (_ : List Val).take _ |>.reverse) h₁ hfi hty hy
      (by simpa using h₂), ?_⟩
    exact allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨⟨_, _, _, _, _, hfi, hty, hcall, hvs, rfl⟩, hl₂⟩⟩
  | callRefNull _ iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .refNull h₁, hl₁⟩
  | @callRefStop _ _ _ _ _ _ _ _ _ _ _ _ _ _ fl _ hfi hty hy hcall hfl iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha
    cases fl with
    | trap =>
      exact ⟨_, .refTrap h₁ hfi hty hy, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall,
        allOk_nil C⟩⟩⟩
    | throw t =>
      exact ⟨_, .refThrow h₁ hfi hty hy, allOk_append.2 ⟨hl₁, allOk_cons.2 ⟨hcall,
        allOk_nil C⟩⟩⟩
    | _ => exact absurd hfl id
  | tail _ hres hfi hty hy iha =>
    obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .tail h₁ hres hfi hty hy, hl₁⟩
  | tailRes _ hres iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .tailRes h₁ hres, hl₁⟩
  | throw _ ht he hn iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .throw h₁ ht he hn, hl₁⟩
  | throwRefNull _ iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .throwRefNull h₁, hl₁⟩
  | throwRefExn _ iha => obtain ⟨l₁, h₁, hl₁⟩ := iha; exact ⟨_, .throwRefExn h₁, hl₁⟩
  | tryOk har _ hvs _ ihb ihk =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihb; obtain ⟨l₂, h₂, hl₂⟩ := ihk
    exact ⟨_, .tryOk har h₁ hvs h₂, allOk_append.2 ⟨hl₁, hl₂⟩⟩
  | tryBrk har _ ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .tryBrk har h₁, hl₁⟩
  | tryEsc har _ ho hnt ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .tryEsc har h₁ ho hnt, hl₁⟩
  | tryCatch har _ hc ihb => obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .tryCatch har h₁ hc, hl₁⟩
  | tryRethrow har _ hc ihb =>
    obtain ⟨l₁, h₁, hl₁⟩ := ihb; exact ⟨_, .tryRethrow har h₁ hc, hl₁⟩

theorem closeOk_ret {C : CallRel H} {a : Nat} {args ws : List Val} {s₁ s₂ : Store H}
    (h : CloseOk C (SCall.mk a args s₁ (.inl (.inl ws)) s₂)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl : Flow) (vs : List Val),
      s₁.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      C s₁ a args (s₂, fl) ∧ fl.retVals = some vs ∧ ws = (vs.take rs.length).reverse := h

theorem closeOk_throw {C : CallRel H} {a : Nat} {args : List Val} {s₁ s₂ : Store H} {t : Nat}
    (h : CloseOk C (SCall.mk a args s₁ (.inl (.inr t)) s₂)) : C s₁ a args (s₂, .throw t) := h

theorem closeOk_trap {C : CallRel H} {a : Nat} {args : List Val} {s₁ s₂ : Store H}
    (h : CloseOk C (SCall.mk a args s₁ (.inr ()) s₂)) : C s₁ a args (s₂, .trap) := h

/-- **Logged runs answered by `C` are closed runs.** -/
theorem logged_closed {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {l : List (SCall H)} {r : Store H × Frame × POut}
    (h : EvalLXPS s f stk es l r) (hl : AllOk C l) : EvalOXP C s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ ho ih => exact .argsAbort (ih hl) ho
  | callRet _ hfi hty _ iha ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    obtain ⟨he, hl₃⟩ := allOk_cons.1 hl₂
    obtain ⟨fi', ps', rs', fl, vs, hfa, hty', hcall, hvs, rfl⟩ := closeOk_ret he
    rw [func?_funcs hfi] at hfa; cases hfa
    rw [hty] at hty'; cases hty'
    exact .callOk (iha hl₁) hfi hty hcall hvs (by simpa using ihk hl₃)
  | callThrow _ hfi hty iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callThrow (iha hl₁) hfi hty (closeOk_throw (allOk_cons.1 hl₂).1)
  | callTrap _ hfi hty iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callTrap (iha hl₁) hfi hty (closeOk_trap (allOk_cons.1 hl₂).1)
  | opOk hi _ hflat _ iha ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .opOk hi (iha hl₁) hflat (ihk hl₂)
  | opStop hi _ hflat hfl iha => exact .opStop hi (iha hl) hflat hfl
  | blockOk har _ hvs _ ihb ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .blockOk har (ihb hl₁) hvs (ihk hl₂)
  | blockBrk har _ ihb => exact .blockBrk har (ihb hl)
  | blockEsc har _ ho ihb => exact .blockEsc har (ihb hl) ho
  | loopOk har _ _ ihb ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .loopOk har (ihb hl₁) (ihk hl₂)
  | loopBack har _ _ ihb ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .loopBack har (ihb hl₁) (ihk hl₂)
  | loopBrk har _ ihb => exact .loopBrk har (ihb hl)
  | loopEsc har _ ho ihb => exact .loopEsc har (ihb hl) ho
  | ifOk _ hb har _ hvs _ ihc iha ihk =>
    obtain ⟨hl₁₂, hl₃⟩ := allOk_append.1 hl
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl₁₂
    exact .ifOk (ihc hl₁) hb har (iha hl₂) hvs (ihk hl₃)
  | ifBrk _ hb har _ ihc iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .ifBrk (ihc hl₁) hb har (iha hl₂)
  | ifEsc _ hb har _ ho ihc iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .ifEsc (ihc hl₁) hb har (iha hl₂) ho
  | ifAbort _ ho ihc => exact .ifAbort (ihc hl) ho
  | indRet _ hres hfi hty hy _ iha ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    obtain ⟨he, hl₃⟩ := allOk_cons.1 hl₂
    obtain ⟨fi', ps', rs', fl, vs, hfa, hty', hcall, hvs, rfl⟩ := closeOk_ret he
    rw [hfi] at hfa; cases hfa
    rw [hty] at hty'; cases hty'
    exact .callIndOk (iha hl₁) hres hfi hty hy hcall hvs (by simpa using ihk hl₃)
  | indThrow _ hres hfi hty hy iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callIndStop (iha hl₁) hres hfi hty hy (closeOk_throw (allOk_cons.1 hl₂).1) trivial
  | indTrap _ hres hfi hty hy iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callIndStop (iha hl₁) hres hfi hty hy (closeOk_trap (allOk_cons.1 hl₂).1) trivial
  | indRes _ hres iha => exact .callIndRes (iha hl) hres
  | refRet _ hfi hty hy _ iha ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    obtain ⟨he, hl₃⟩ := allOk_cons.1 hl₂
    obtain ⟨fi', ps', rs', fl, vs, hfa, hty', hcall, hvs, rfl⟩ := closeOk_ret he
    rw [hfi] at hfa; cases hfa
    rw [hty] at hty'; cases hty'
    exact .callRefOk (iha hl₁) hfi hty hy hcall hvs (by simpa using ihk hl₃)
  | refThrow _ hfi hty hy iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callRefStop (iha hl₁) hfi hty hy (closeOk_throw (allOk_cons.1 hl₂).1) trivial
  | refTrap _ hfi hty hy iha =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .callRefStop (iha hl₁) hfi hty hy (closeOk_trap (allOk_cons.1 hl₂).1) trivial
  | refNull _ iha => exact .callRefNull (iha hl)
  | tail _ hres hfi hty hy iha => exact .tail (iha hl) hres hfi hty hy
  | tailRes _ hres iha => exact .tailRes (iha hl) hres
  | throw _ ht he hn iha => exact .throw (iha hl) ht he hn
  | throwRefNull _ iha => exact .throwRefNull (iha hl)
  | throwRefExn _ iha => exact .throwRefExn (iha hl)
  | tryOk har _ hvs _ ihb ihk =>
    obtain ⟨hl₁, hl₂⟩ := allOk_append.1 hl
    exact .tryOk har (ihb hl₁) hvs (ihk hl₂)
  | tryBrk har _ ihb => exact .tryBrk har (ihb hl)
  | tryEsc har _ ho hnt ihb => exact .tryEsc har (ihb hl) ho hnt
  | tryCatch har _ hc ihb => exact .tryCatch har (ihb hl) hc
  | tryRethrow har _ hc ihb => exact .tryRethrow har (ihb hl) hc

end Silmaril.Wasm.Cfg.Proofs.MachineLClosed
