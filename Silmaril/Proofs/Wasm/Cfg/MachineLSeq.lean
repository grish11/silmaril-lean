module

public import Silmaril.Wasm.Cfg.MachineL.Defs

@[expose] public section

/-!
# The logged relation over sequences (H1 support)

`append`: an `EvalLXPS` run of `es₁` that ends abruptly is a run of `es₁ ++ es₂` with the same
log and end; one that falls through continues into a run of `es₂`, the logs concatenated.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLSeq

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **Sequencing.** -/
theorem append {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) (es₂ : List BExpr) :
    (¬ r.2.2.IsNormal → EvalLXPS s f stk (es ++ es₂) l r) ∧
    (∀ s₁ f₁ stk₁, r = (s₁, f₁, .flow (.normal stk₁)) → ∀ l₂ r₂,
      EvalLXPS s₁ f₁ stk₁ es₂ l₂ r₂ → EvalLXPS s f stk (es ++ es₂) (l ++ l₂) r₂) := by
  induction h with
  | nil =>
    refine ⟨fun hn => absurd trivial hn, fun _ _ _ heq _ _ h₂ => ?_⟩
    simp only [Prod.mk.injEq, POut.flow.injEq, Flow.normal.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simpa using h₂
  | argsAbort hargs ho =>
    exact ⟨fun _ => .argsAbort hargs ho, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq; exact absurd trivial ho⟩
  | callRet hargs hfi hty hk _ ihk =>
    refine ⟨fun hn => .callRet hargs hfi hty (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .callRet hargs hfi hty (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | callThrow hargs hfi hty =>
    exact ⟨fun _ => .callThrow hargs hfi hty, fun _ _ _ heq => by simp at heq⟩
  | callTrap hargs hfi hty =>
    exact ⟨fun _ => .callTrap hargs hfi hty, fun _ _ _ heq => by simp at heq⟩
  | opOk hi hargs hflat hk _ ihk =>
    refine ⟨fun hn => .opOk hi hargs hflat (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .opOk hi hargs hflat (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | opStop hi hargs hflat hfl =>
    exact ⟨fun _ => .opStop hi hargs hflat hfl, fun _ _ _ heq => by
      simp only [Prod.mk.injEq, POut.flow.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq
      exact absurd trivial hfl⟩
  | blockOk har hbody hvs hk _ ihk =>
    refine ⟨fun hn => .blockOk har hbody hvs (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .blockOk har hbody hvs (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | blockBrk har hbody =>
    exact ⟨fun _ => .blockBrk har hbody, fun _ _ _ heq => by simp at heq⟩
  | blockEsc har hbody ho =>
    exact ⟨fun _ => .blockEsc har hbody ho, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq
      simp [POut.Escapes, Flow.Escapes] at ho⟩
  | loopOk har hbody hk _ ihk =>
    refine ⟨fun hn => .loopOk har hbody (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .loopOk har hbody (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | loopBack har hbody hk _ ihk =>
    refine ⟨fun hn => .loopBack har hbody (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .loopBack har hbody (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | loopBrk har hbody =>
    exact ⟨fun _ => .loopBrk har hbody, fun _ _ _ heq => by simp at heq⟩
  | loopEsc har hbody ho =>
    exact ⟨fun _ => .loopEsc har hbody ho, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq
      simp [POut.Escapes, Flow.Escapes] at ho⟩
  | ifOk hc hb har harm hvs hk _ _ ihk =>
    refine ⟨fun hn => .ifOk hc hb har harm hvs (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    have := EvalLXPS.ifOk hc hb har harm hvs (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
    simpa only [List.cons_append, List.append_assoc] using this
  | ifBrk hc hb har harm =>
    exact ⟨fun _ => .ifBrk hc hb har harm, fun _ _ _ heq => by simp at heq⟩
  | ifEsc hc hb har harm ho =>
    exact ⟨fun _ => .ifEsc hc hb har harm ho, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq
      simp [POut.Escapes, Flow.Escapes] at ho⟩
  | ifAbort hc ho =>
    exact ⟨fun _ => .ifAbort hc ho, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq; exact absurd trivial ho⟩
  | indRet hargs hres hfi hty hy hk _ ihk =>
    refine ⟨fun hn => .indRet hargs hres hfi hty hy (ihk.1 hn),
      fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .indRet hargs hres hfi hty hy (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | indThrow hargs hres hfi hty hy =>
    exact ⟨fun _ => .indThrow hargs hres hfi hty hy, fun _ _ _ heq => by simp at heq⟩
  | indTrap hargs hres hfi hty hy =>
    exact ⟨fun _ => .indTrap hargs hres hfi hty hy, fun _ _ _ heq => by simp at heq⟩
  | indRes hargs hres =>
    exact ⟨fun _ => .indRes hargs hres, fun _ _ _ heq => by simp at heq⟩
  | refRet hargs hfi hty hy hk _ ihk =>
    refine ⟨fun hn => .refRet hargs hfi hty hy (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .refRet hargs hfi hty hy (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | refThrow hargs hfi hty hy =>
    exact ⟨fun _ => .refThrow hargs hfi hty hy, fun _ _ _ heq => by simp at heq⟩
  | refTrap hargs hfi hty hy =>
    exact ⟨fun _ => .refTrap hargs hfi hty hy, fun _ _ _ heq => by simp at heq⟩
  | refNull hargs =>
    exact ⟨fun _ => .refNull hargs, fun _ _ _ heq => by simp at heq⟩
  | tail hargs hres hfi hty hy =>
    exact ⟨fun _ => .tail hargs hres hfi hty hy, fun _ _ _ heq => by simp at heq⟩
  | tailRes hargs hres =>
    exact ⟨fun _ => .tailRes hargs hres, fun _ _ _ heq => by simp at heq⟩
  | throw hargs ht he hn =>
    exact ⟨fun _ => .throw hargs ht he hn, fun _ _ _ heq => by simp at heq⟩
  | throwRefNull hargs =>
    exact ⟨fun _ => .throwRefNull hargs, fun _ _ _ heq => by simp at heq⟩
  | throwRefExn hargs =>
    exact ⟨fun _ => .throwRefExn hargs, fun _ _ _ heq => by simp at heq⟩
  | tryOk har hbody hvs hk _ ihk =>
    refine ⟨fun hn => .tryOk har hbody hvs (ihk.1 hn), fun s₁ f₁ stk₁ heq l₂ r₂ h₂ => ?_⟩
    simpa [List.append_assoc] using .tryOk har hbody hvs (ihk.2 s₁ f₁ stk₁ heq l₂ r₂ h₂)
  | tryBrk har hbody =>
    exact ⟨fun _ => .tryBrk har hbody, fun _ _ _ heq => by simp at heq⟩
  | tryEsc har hbody ho hnt =>
    exact ⟨fun _ => .tryEsc har hbody ho hnt, fun _ _ _ heq => by
      simp only [Prod.mk.injEq] at heq; obtain ⟨-, -, rfl⟩ := heq
      simp [POut.Escapes, Flow.Escapes] at ho⟩
  | tryCatch har hbody hc =>
    exact ⟨fun _ => .tryCatch har hbody hc, fun _ _ _ heq => by simp at heq⟩
  | tryRethrow har hbody hc =>
    exact ⟨fun _ => .tryRethrow har hbody hc, fun _ _ _ heq => by simp at heq⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLSeq
