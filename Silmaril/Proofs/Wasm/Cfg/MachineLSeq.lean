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

/-- Flat instructions keep the frame's instance. -/
theorem evalFlat_module {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    (h : evalFlat s f stk i = some (s', f', fl)) : f'.module = f.module := by
  unfold evalFlat at h
  repeat' (first | split at h | (simp only [Option.map_eq_some_iff, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl)
    | (obtain ⟨_, -, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl, -⟩ := h; rfl)
    | (simp at h; done)
    | (obtain ⟨_, -, _, -, -, rfl, -⟩ := h; rfl)
    | (obtain ⟨a, -, b, -, h⟩ := h
       split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl))

/-- **The logged relation keeps the frame's instance.** -/
theorem module_eq {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    r.2.1.module = f.module := by
  induction h <;> (try have := evalFlat_module ‹evalFlat _ _ _ _ = _›) <;> simp_all

theorem liftInstrs_append (is js : List Instr) :
    liftInstrs (is ++ js) = liftInstrs is ++ liftInstrs js := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [liftInstrs, ih]

/-- The outcome of splitting a run of `es₁ ++ es₂`. -/
def SplitRes (s : Store H) (f : Frame) (stk : List Val) (es₁ es₂ : List BExpr) (l : List (SCall H))
    (r : Store H × Frame × POut) : Prop :=
  (∃ s₁ f₁ stk₁ l₁ l₂, EvalLXPS s f stk es₁ l₁ (s₁, f₁, .flow (.normal stk₁)) ∧
    EvalLXPS s₁ f₁ stk₁ es₂ l₂ r ∧ l = l₁ ++ l₂) ∨
  (EvalLXPS s f stk es₁ l r ∧ ¬ r.2.2.IsNormal)

theorem escapes_not_normal {o : POut} (h : o.Escapes) : ¬ o.IsNormal := by
  rcases o with fl | _
  · cases fl <;> simp_all [POut.Escapes, POut.IsNormal, Flow.Escapes, Flow.IsNormal]
  · exact id

/-- A rule continuing with `hk` on the rest: splitting the whole is splitting the rest. -/
theorem split_cont {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {y : BExpr}
    {pre : List (SCall H)}
    (A : ∀ {es : List BExpr} {l : List (SCall H)} {r : Store H × Frame × POut},
      EvalLXPS s₁ f₁ stk₁ es l r → EvalLXPS s f stk (y :: es) (pre ++ l) r)
    {es₁ es₂ : List BExpr} {l : List (SCall H)} {r : Store H × Frame × POut}
    (hk : EvalLXPS s₁ f₁ stk₁ (es₁ ++ es₂) l r)
    (ih : ∀ z es₁', es₁ = z :: es₁' → SplitRes s₁ f₁ stk₁ (z :: es₁') es₂ l r) :
    SplitRes s f stk (y :: es₁) es₂ (pre ++ l) r := by
  rcases es₁ with _ | ⟨z, es₁'⟩
  · exact .inl ⟨s₁, f₁, stk₁, pre ++ [], l, A .nil, hk, by simp⟩
  · rcases ih z es₁' rfl with ⟨s₂, f₂, stk₂, l₁, l₂, h₁, h₂, rfl⟩ | ⟨h₁, hn⟩
    · exact .inl ⟨s₂, f₂, stk₂, pre ++ l₁, l₂, A h₁, h₂, by simp⟩
    · exact .inr ⟨A h₁, hn⟩

theorem split_cons {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    ∀ y es₁ es₂, es = y :: (es₁ ++ es₂) → SplitRes s f stk (y :: es₁) es₂ l r := by
  induction h with
  | nil => intro _ _ _ he; cases he
  | argsAbort hargs ho =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.argsAbort hargs ho, ho⟩
  | callRet hargs hfi hty hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have := split_cont (pre := _ ++ [_]) (fun h => by simpa using EvalLXPS.callRet hargs hfi hty h)
      hk
        (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
    rwa [List.append_assoc, List.singleton_append] at this
  | callThrow hargs hfi hty =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.callThrow hargs hfi hty, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | callTrap hargs hfi hty =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.callTrap hargs hfi hty, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | opOk hi hargs hflat hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact split_cont (fun h => EvalLXPS.opOk hi hargs hflat h) hk
      (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
  | opStop hi hargs hflat hfl =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.opStop hi hargs hflat hfl, hfl⟩
  | blockOk har hbody hvs hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact split_cont (fun h => EvalLXPS.blockOk har hbody hvs h) hk
      (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
  | blockBrk har hbody =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.blockBrk har hbody, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | blockEsc har hbody ho =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.blockEsc har hbody ho, escapes_not_normal ho⟩
  | loopOk har hbody hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact split_cont (fun h => EvalLXPS.loopOk har hbody h) hk
      (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
  | @loopBack s s₁ f f₁ stk vs bt body es np nr l₁ l₂ r har hbody hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rcases ihk (.loop bt body) es₁ es₂ rfl with ⟨s₂, f₂, stk₂, l₃, l₄, h₁, h₂, rfl⟩ | ⟨h₁, hn⟩
    · exact .inl ⟨s₂, f₂, stk₂, l₁ ++ l₃, l₄, .loopBack har hbody h₁, h₂, by simp⟩
    · exact .inr ⟨.loopBack har hbody h₁, hn⟩
  | loopBrk har hbody =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.loopBrk har hbody, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | loopEsc har hbody ho =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.loopEsc har hbody ho, escapes_not_normal ho⟩
  | ifOk hc hb har harm hvs hk _ _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact split_cont (fun h => EvalLXPS.ifOk hc hb har harm hvs h) hk
      (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
  | ifBrk hc hb har harm =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.ifBrk hc hb har harm, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | ifEsc hc hb har harm ho =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.ifEsc hc hb har harm ho, escapes_not_normal ho⟩
  | ifAbort hc ho =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.ifAbort hc ho, ho⟩
  | indRet hargs hres hfi hty hy hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have := split_cont (pre := _ ++ [_]) (fun h => by simpa using EvalLXPS.indRet hargs hres hfi hty hy h)
      hk (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
    rwa [List.append_assoc, List.singleton_append] at this
  | indThrow hargs hres hfi hty hy =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.indThrow hargs hres hfi hty hy, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | indTrap hargs hres hfi hty hy =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.indTrap hargs hres hfi hty hy, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | indRes hargs hres =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.indRes hargs hres, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | refRet hargs hfi hty hy hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have := split_cont (pre := _ ++ [_]) (fun h => by simpa using EvalLXPS.refRet hargs hfi hty hy h)
      hk (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
    rwa [List.append_assoc, List.singleton_append] at this
  | refThrow hargs hfi hty hy =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.refThrow hargs hfi hty hy, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | refTrap hargs hfi hty hy =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.refTrap hargs hfi hty hy, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | refNull hargs =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.refNull hargs, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | tail hargs hres hfi hty hy =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tail hargs hres hfi hty hy, id⟩
  | tailRes hargs hres =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tailRes hargs hres, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | throw hargs ht he' hn =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.throw hargs ht he' hn, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | throwRefNull hargs =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.throwRefNull hargs, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | throwRefExn hargs =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.throwRefExn hargs, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | tryOk har hbody hvs hk _ ihk =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact split_cont (fun h => EvalLXPS.tryOk har hbody hvs h) hk
      (fun z es₁' he => ihk z es₁' es₂ (by simp [he]))
  | tryBrk har hbody =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tryBrk har hbody, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | tryEsc har hbody ho hnt =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tryEsc har hbody ho hnt, escapes_not_normal ho⟩
  | tryCatch har hbody hc =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tryCatch har hbody hc, by simp [POut.IsNormal, Flow.IsNormal]⟩
  | tryRethrow har hbody hc =>
    intro y es₁ es₂ he; simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .inr ⟨.tryRethrow har hbody hc, by simp [POut.IsNormal, Flow.IsNormal]⟩

/-- **Splitting a sequence** (the converse of `append`): a run of `es₁ ++ es₂` is a run of `es₁`
falling through, then a run of `es₂`, the logs concatenated; or a run of `es₁` ending abruptly,
with the whole log and end. -/
theorem split {s : Store H} {f : Frame} {stk : List Val} (es₁ es₂ : List BExpr)
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk (es₁ ++ es₂) l r) :
    SplitRes s f stk es₁ es₂ l r := by
  rcases es₁ with _ | ⟨y, es₁⟩
  · exact .inl ⟨s, f, stk, [], l, .nil, h, rfl⟩
  · exact split_cons h y es₁ es₂ rfl

end Silmaril.Wasm.Cfg.Proofs.MachineLSeq
