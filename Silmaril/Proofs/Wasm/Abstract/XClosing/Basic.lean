module

public import Silmaril.Wasm.Abstract.XClosing.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Proofs.Wasm.Abstract.Closing.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.XClosing.Thms`: `Shape.close wasmOpenX` is the
closed extended call relation `closedCallX`, read through exit flows. The proof
is `Closing`'s, with the indirect, reference and tail call cases added:

* `close_leX`: answering a logged extended run's calls by closed calls gives an
  `EvalOX` run (`evalOX_of_evalLX`); a callee trap stops it with a trap there
  (for a tail call too: the caller's flow is the callee's trap).
* `le_closeX`: an `EvalOX` run whose calls are answered by `close wasmOpenX` is
  a logged run whose log `Shape.Subst` resolves (`evalLX_of_evalOX`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XClosing
open Silmaril.Proofs.Wasm.Abstract.Closing

variable {H : Type}

theorem tailFlow_of_retVals {n : Nat} {fl : Flow} {vs : List Val} (h : fl.retVals = some vs) :
    tailFlow n fl = .ret (vs.take n) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | x <;> simp_all [Flow.retVals, tailFlow]

/-- A logged run whose calls all return in `toClosed C` is an `EvalOX C` run; one
with a trapping call is an `EvalOX C` run that traps. -/
theorem evalOX_of_evalLX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {l : List (OCall H)} {r : Store H × Frame × Flow}
    (h : EvalLX s f stk es l r) :
    (AllRet (toClosed C) l → EvalOX C s f stk es r) ∧
      (TrapAt (toClosed C) l → ∃ s' f', EvalOX C s f stk es (s', f', .trap)) := by
  induction h with
  | nil => exact ⟨fun _ => .nil, fun h => absurd h trapAt_nil⟩
  | argsAbort _ hfl ih =>
    exact ⟨fun h => .argsAbort (ih.1 h) hfl, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | callRet _ hfi hty _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl h.2.1 (funcs_of_func? hfi) hty
      exact .callOk (ih₁.1 h.1) hfi hty hC hvs (hws ▸ ih₂.1 h.2.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callTrap (ih₁.1 hu) hfi hty hC⟩
        | there hz h =>
          obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl hz (funcs_of_func? hfi) hty
          obtain ⟨s', f', d⟩ := ih₂.2 h
          exact ⟨s', f', .callOk (ih₁.1 hu) hfi hty hC hvs (hws ▸ d)⟩
  | callThrow _ hfi hty ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      exact .callThrow (ih.1 h.1) hfi hty (ret_inr h.2.1)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callTrap (ih.1 hu) hfi hty hC⟩
        | there _ h => exact absurd h trapAt_nil
  | opOk hi _ hflat _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .opOk hi (ih₁.1 h.1) hflat (ih₂.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .opOk hi (ih₁.1 hu) hflat d⟩
  | opStop hi _ hflat hfl ih =>
    exact ⟨fun h => .opStop hi (ih.1 h) hflat hfl, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .blockOk har (ih₁.1 h.1) hvs (ih₂.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .blockEsc har d trivial⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .blockOk har (ih₁.1 hu) hvs d⟩
  | blockBrk har _ ih =>
    exact ⟨fun h => .blockBrk har (ih.1 h), fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .blockEsc har d trivial⟩⟩
  | blockEsc har _ hfl ih =>
    exact ⟨fun h => .blockEsc har (ih.1 h) hfl, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .blockEsc har d trivial⟩⟩
  | loopOk har _ _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .loopOk har (ih₁.1 h.1) (ih₂.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .loopEsc har d trivial⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .loopOk har (ih₁.1 hu) d⟩
  | loopBack har _ _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .loopBack har (ih₁.1 h.1) (ih₂.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .loopEsc har d trivial⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .loopBack har (ih₁.1 hu) d⟩
  | loopBrk har _ ih =>
    exact ⟨fun h => .loopBrk har (ih.1 h), fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .loopEsc har d trivial⟩⟩
  | loopEsc har _ hfl ih =>
    exact ⟨fun h => .loopEsc har (ih.1 h) hfl, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .loopEsc har d trivial⟩⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_append] at h
      exact .ifOk (ih₁.1 h.1.1) hb har (ih₂.1 h.1.2) hvs (ih₃.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · rcases trapAt_append h with h | ⟨hu', h⟩
        · obtain ⟨s', f', d⟩ := ih₁.2 h
          exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
        · obtain ⟨s', f', d⟩ := ih₂.2 h
          exact ⟨s', f', .ifEsc (ih₁.1 hu') hb har d trivial⟩
      · rw [allRet_append] at hu
        obtain ⟨s', f', d⟩ := ih₃.2 h
        exact ⟨s', f', .ifOk (ih₁.1 hu.1) hb har (ih₂.1 hu.2) hvs d⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .ifBrk (ih₁.1 h.1) hb har (ih₂.1 h.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .ifEsc (ih₁.1 hu) hb har d trivial⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append] at h
      exact .ifEsc (ih₁.1 h.1) hb har (ih₂.1 h.2) hfl
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
      · obtain ⟨s', f', d⟩ := ih₂.2 h
        exact ⟨s', f', .ifEsc (ih₁.1 hu) hb har d trivial⟩
  | ifAbort _ hfl ih =>
    exact ⟨fun h => .ifAbort (ih.1 h) hfl, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .ifAbort d Flow.notNormal_trap⟩⟩
  | callIndRet _ hres hfi hty _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl h.2.1 hfi hty
      exact .callIndOk (ih₁.1 h.1) hres hfi hty hC hvs (hws ▸ ih₂.1 h.2.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callIndStop (ih₁.1 hu) hres hfi hty hC trivial⟩
        | there hz h =>
          obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl hz hfi hty
          obtain ⟨s', f', d⟩ := ih₂.2 h
          exact ⟨s', f', .callIndOk (ih₁.1 hu) hres hfi hty hC hvs (hws ▸ d)⟩
  | callIndThrow _ hres hfi hty ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      exact .callIndStop (ih.1 h.1) hres hfi hty (ret_inr h.2.1) trivial
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callIndStop (ih.1 hu) hres hfi hty hC trivial⟩
        | there _ h => exact absurd h trapAt_nil
  | callIndRes _ hres ih =>
    exact ⟨fun h => .callIndRes (ih.1 h) hres, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | callRefRet _ hfi hty _ ih₁ ih₂ =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl h.2.1 hfi hty
      exact .callRefOk (ih₁.1 h.1) hfi hty hC hvs (hws ▸ ih₂.1 h.2.2)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callRefStop (ih₁.1 hu) hfi hty hC trivial⟩
        | there hz h =>
          obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl hz hfi hty
          obtain ⟨s', f', d⟩ := ih₂.2 h
          exact ⟨s', f', .callRefOk (ih₁.1 hu) hfi hty hC hvs (hws ▸ d)⟩
  | callRefThrow _ hfi hty ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      exact .callRefStop (ih.1 h.1) hfi hty (ret_inr h.2.1) trivial
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .callRefStop (ih.1 hu) hfi hty hC trivial⟩
        | there _ h => exact absurd h trapAt_nil
  | callRefNull _ ih =>
    exact ⟨fun h => .callRefNull (ih.1 h), fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | @tailRet s s₁ s₂ f f₁ stk stk₁ ws i args es fa fi ps rs l₁ _ hres hfi hty ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inl h.2.1 hfi hty
      have d := EvalOX.tail (es := es) (ih.1 h.1) hres hfi hty hC (.inl ⟨vs, hvs⟩)
      rwa [tailFlow_of_retVals hvs, ← hws] at d
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .tail (ih.1 hu) hres hfi hty hC (.inr trivial)⟩
        | there _ h => exact absurd h trapAt_nil
  | tailThrow _ hres hfi hty ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [allRet_append, allRet_cons] at h
      exact .tail (ih.1 h.1) hres hfi hty (ret_inr h.2.1) (.inr trivial)
    · rcases trapAt_append h with h | ⟨hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 h
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · cases h with
        | here h =>
          obtain ⟨s', hC⟩ := traps_toClosed h
          exact ⟨s', _, .tail (ih.1 hu) hres hfi hty hC (.inr trivial)⟩
        | there _ h => exact absurd h trapAt_nil
  | tailRes _ hres ih =>
    exact ⟨fun h => .tailRes (ih.1 h) hres, fun h =>
      let ⟨s', f', d⟩ := ih.2 h; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩

theorem close_leX : Shape.close (wasmOpenX (H := H)) ≤ toClosed closedCallX := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, hE, hx, he⟩, hS⟩
  have close : ∀ {s'' f'' bfl'}, EvalOX closedCallX s (Frame.forCall fi.module vs fn.locals) []
      (liftInstrs fn.body) (s'', f'', bfl') → closedCallX s a vs (s'', bfl') := fun d => by
    rw [closedCallX_fixpoint]
    exact ⟨fi, fn, ps, rs, _, hfi, hc, hty, d⟩
  rcases subst_cases hS with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨rfl, z, -, hz⟩
  · exact ⟨fi, ps, rs, s', bfl, fl, hfi, hty, close ((evalOX_of_evalLX hE).1 h), hx, by rw [he]⟩
  · obtain ⟨s'', f'', d⟩ := (evalOX_of_evalLX hE).2 h
    exact ⟨fi, ps, rs, s'', .trap, .trap, hfi, hty, close d, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, -, _, _, _, _, _, _, -, -, -, -, hy⟩ := hz
    exact absurd (Prod.mk.inj hy).2.symm (endOfFlow_ne_div _ _)

/-- An `EvalO` run whose calls are answered by `ofClosed c` is mirrored by a
logged run. -/
theorem evalLX_of_evalOX {c : (wasmOShape H).ClosedMod} {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : EvalOX (ofClosed c) s f stk es r) :
    ∃ l r', EvalLX s f stk es l r' ∧ Mirrors c r l r' := by
  induction h with
  | nil => exact ⟨[], _, .nil, .inl ⟨allRet_nil c, rfl⟩⟩
  | argsAbort _ hfl ih =>
    obtain ⟨l, r', d, h⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, .argsAbort d hfl, .inl ⟨h, rfl⟩⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, .argsAbort d Flow.notNormal_throw, .inr ⟨h₁, h₂, t, rfl⟩⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    have hz := ret_ofClosed_inl hcall (funcs_of_func? hfi) hty hvs
    have d := EvalLX.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂)
    refine ⟨_, _, d, ?_⟩
    rw [← List.singleton_append, ← List.append_assoc]
    exact Mirrors.append (allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩) h₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    have hz : Traps c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr 0) s₂) :=
      ⟨_, _, _, _, _, rfl, hcall fi ps rs .trap (funcs_of_func? hfi) hty rfl⟩
    exact ⟨_, _, EvalLX.callThrow (t := 0) (s₂ := s₂) d₁ hfi hty,
      .inr ⟨rfl, trapAt_append_right h₁ (.here hz), 0, rfl⟩⟩
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    have hz : Ret c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂) :=
      ⟨_, _, _, _, _, rfl, hcall fi ps rs (.throw t) (funcs_of_func? hfi) hty rfl⟩
    exact ⟨_, _, EvalLX.callThrow (t := t) (s₂ := s₂) d₁ hfi hty,
      .inl ⟨allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩, rfl⟩⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    exact ⟨_, _, .opOk hi d₁ hflat d₂, h₂.append h₁⟩
  | opStop hi _ hflat hfl ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, .opStop hi d₁ hflat hfl, .inl ⟨h₁, rfl⟩⟩
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    exact ⟨_, _, .blockOk har d₁ hvs d₂, h₂.append h₁⟩
  | blockBrk har _ ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, .blockBrk har d₁, .inl ⟨h₁, rfl⟩⟩
  | blockEsc har _ hfl ih =>
    obtain ⟨l, r', d, h⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, .blockEsc har d hfl, .inl ⟨h, rfl⟩⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, .blockEsc har d trivial, .inr ⟨h₁, h₂, t, rfl⟩⟩
  | loopOk har _ _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    exact ⟨_, _, .loopOk har d₁ d₂, h₂.append h₁⟩
  | loopBack har _ _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    exact ⟨_, _, .loopBack har d₁ d₂, h₂.append h₁⟩
  | loopBrk har _ ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨_, _, .loopBrk har d₁, .inl ⟨h₁, rfl⟩⟩
  | loopEsc har _ hfl ih =>
    obtain ⟨l, r', d, h⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, .loopEsc har d hfl, .inl ⟨h, rfl⟩⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, .loopEsc har d trivial, .inr ⟨h₁, h₂, t, rfl⟩⟩
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c' t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, m₂⟩ := ih₂
    obtain ⟨h₂, rfl⟩ := m₂.normal (by rintro (h : fl = .trap); subst h; simp [Flow.blockVals] at hvs)
    obtain ⟨l₃, r₃, d₃, h₃⟩ := ih₃
    exact ⟨_, _, .ifOk d₁ hb har d₂ hvs d₃, h₃.append (allRet_append.2 ⟨h₁, h₂⟩)⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, m₂⟩ := ih₂
    obtain ⟨h₂, rfl⟩ := m₂.normal nofun
    exact ⟨_, _, .ifBrk d₁ hb har d₂, .inl ⟨allRet_append.2 ⟨h₁, h₂⟩, rfl⟩⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    rcases h₂ with ⟨h₂, rfl⟩ | ⟨h₂₁, h₂₂, t, h₂₃⟩
    · exact ⟨_, _, .ifEsc d₁ hb har d₂ hfl, .inl ⟨allRet_append.2 ⟨h₁, h₂⟩, rfl⟩⟩
    · obtain ⟨s', f', fl'⟩ := r₂
      subst h₂₃
      exact ⟨_, _, .ifEsc d₁ hb har d₂ trivial, .inr ⟨h₂₁, trapAt_append_right h₁ h₂₂, t, rfl⟩⟩
  | ifAbort _ hfl ih =>
    obtain ⟨l, r', d, h⟩ := ih
    rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
    · exact ⟨l, _, .ifAbort d hfl, .inl ⟨h, rfl⟩⟩
    · obtain ⟨s', f', fl'⟩ := r'
      subst h₃
      exact ⟨l, _, .ifAbort d Flow.notNormal_throw, .inr ⟨h₁, h₂, t, rfl⟩⟩
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r _ hres hfi hty hcall hvs _
      ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    have hz := ret_ofClosed_inl hcall hfi hty hvs
    have d := EvalLX.callIndRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hres hfi hty
      (by rw [List.reverse_reverse]; exact d₂)
    refine ⟨_, _, d, ?_⟩
    rw [← List.singleton_append, ← List.append_assoc]
    exact Mirrors.append (allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩) h₂
  | callIndRes _ hres ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨l₁, _, .callIndRes d₁ hres, .inl ⟨h₁, rfl⟩⟩
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    cases fl with
    | trap =>
      have hz : Traps c (OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr 0) s₂) :=
        ⟨_, _, _, _, _, rfl, hcall fi ps rs .trap hfi hty rfl⟩
      exact ⟨_, _, EvalLX.callIndThrow (t := 0) (s₂ := s₂) d₁ hres hfi hty,
        .inr ⟨rfl, trapAt_append_right h₁ (.here hz), 0, rfl⟩⟩
    | throw t =>
      have hz : Ret c (OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂) :=
        ⟨_, _, _, _, _, rfl, hcall fi ps rs (.throw t) hfi hty rfl⟩
      exact ⟨_, _, EvalLX.callIndThrow (t := t) (s₂ := s₂) d₁ hres hfi hty,
        .inl ⟨allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩, rfl⟩⟩
    | _ => exact absurd hfl id
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih₁
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    obtain ⟨l₂, r₂, d₂, h₂⟩ := ih₂
    have hz := ret_ofClosed_inl hcall hfi hty hvs
    have d := EvalLX.callRefRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) (y := y) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂)
    refine ⟨_, _, d, ?_⟩
    rw [← List.singleton_append, ← List.append_assoc]
    exact Mirrors.append (allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩) h₂
  | callRefNull _ ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨l₁, _, .callRefNull d₁, .inl ⟨h₁, rfl⟩⟩
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl _ hfi hty hcall hfl ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    cases fl with
    | trap =>
      have hz : Traps c (OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr 0) s₂) :=
        ⟨_, _, _, _, _, rfl, hcall fi ps rs .trap hfi hty rfl⟩
      exact ⟨_, _, EvalLX.callRefThrow (t := 0) (s₂ := s₂) (y := y) d₁ hfi hty,
        .inr ⟨rfl, trapAt_append_right h₁ (.here hz), 0, rfl⟩⟩
    | throw t =>
      have hz : Ret c (OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inr t) s₂) :=
        ⟨_, _, _, _, _, rfl, hcall fi ps rs (.throw t) hfi hty rfl⟩
      exact ⟨_, _, EvalLX.callRefThrow (t := t) (s₂ := s₂) (y := y) d₁ hfi hty,
        .inl ⟨allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩, rfl⟩⟩
    | _ => exact absurd hfl id
  | @tail s s₁ s₂ f f₁ stk stk₁ i args es fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    rcases hfl with ⟨vs, hvs⟩ | hab
    · have hz := ret_ofClosed_inl hcall hfi hty hvs
      refine ⟨_, _, EvalLX.tailRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hres hfi hty,
        .inl ⟨allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩, ?_⟩⟩
      rw [List.reverse_reverse, tailFlow_of_retVals hvs]
    · cases fl with
      | trap =>
        have hz : Traps c (OCall.mk fa ((stk₁.drop (tailPop i)).take ps.length).reverse s₁
            (.inr 0) s₂) := ⟨_, _, _, _, _, rfl, hcall fi ps rs .trap hfi hty rfl⟩
        exact ⟨_, _, EvalLX.tailThrow (t := 0) (s₂ := s₂) d₁ hres hfi hty,
          .inr ⟨rfl, trapAt_append_right h₁ (.here hz), 0, rfl⟩⟩
      | throw t =>
        have hz : Ret c (OCall.mk fa ((stk₁.drop (tailPop i)).take ps.length).reverse s₁
            (.inr t) s₂) := ⟨_, _, _, _, _, rfl, hcall fi ps rs (.throw t) hfi hty rfl⟩
        exact ⟨_, _, EvalLX.tailThrow (t := t) (s₂ := s₂) d₁ hres hfi hty,
          .inl ⟨allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩, rfl⟩⟩
      | _ => exact absurd hab id
  | tailRes _ hres ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    exact ⟨l₁, _, .tailRes d₁ hres, .inl ⟨h₁, rfl⟩⟩

theorem closedCallX_le_ofClosed : (closedCallX : CallRel H) ≤ ofClosed (Shape.close wasmOpenX) := by
  refine OrderHom.lfp_le _ ?_
  rintro s a vs ⟨s', bfl⟩ ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩ fi' ps' rs' fl hfi' hty' hx
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  rw [Shape.close, ← OrderHom.map_lfp]
  obtain ⟨l, r', dL, h⟩ := evalLX_of_evalOX d
  rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
  · exact ⟨(l, endOfFlow fl s'), ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, dL, hx, rfl⟩,
      subst_of_allRet h⟩
  · obtain ⟨s'', f'', fl'⟩ := r'
    obtain rfl : bfl = .trap := h₁
    obtain rfl : fl = .trap := by simpa [exitFlow] using hx.symm
    subst h₃
    exact ⟨(l, endOfFlow (.throw t) s''), ⟨fi, fn, ps, rs, s'', f'', .throw t, .throw t, hfi, hc,
      hty, dL, rfl, rfl⟩, subst_of_trapAt h₂⟩

theorem le_closeX : toClosed closedCallX ≤ Shape.close (wasmOpenX (H := H)) := by
  rintro a s vs y ⟨fi, ps, rs, s', bfl, fl, hfi, hty, hC, hx, rfl⟩
  exact closedCallX_le_ofClosed _ _ _ _ hC fi ps rs fl hfi hty hx

theorem close_eqX : Shape.close (wasmOpenX (H := H)) = toClosed closedCallX :=
  le_antisymm close_leX le_closeX

/-- **Closing the open module gives the closed outcomes.** -/
theorem close_wasmOpenX (a : Nat) (s : Store H) (vs : List Val) :
    Shape.close wasmOpenX a s vs =
      {y | ∃ s' fl, ClosedOutcomeX s a vs s' fl ∧ y = ([], endOfFlow fl s')} := by
  rw [close_eqX]
  ext y
  constructor
  · rintro ⟨fi, ps, rs, s', bfl, fl, hfi, hty, hC, hx, rfl⟩
    rw [closedCallX_fixpoint] at hC
    obtain ⟨fi', fn, ps', rs', f₂, hfi', hc, hty', d⟩ := hC
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    exact ⟨s', fl, ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩, rfl⟩
  · rintro ⟨s', fl, ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩, rfl⟩
    refine ⟨fi, ps, rs, s', bfl, fl, hfi, hty, ?_, hx, rfl⟩
    rw [closedCallX_fixpoint]
    exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩

end Silmaril.Proofs.Wasm.Abstract.XClosing
