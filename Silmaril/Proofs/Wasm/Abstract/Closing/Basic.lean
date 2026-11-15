module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
import Silmaril.Proofs.Wasm.Abstract.Recursion.Basic

/-!
# Wasm functions as an open abstract module: proofs

`Shape.close wasmOpen` is the closed call relation `closedCall`, read through
exit flows. Both inclusions are least-fixpoint inductions:

* `close_le`: answering a logged run's calls by closed calls gives an `EvalO`
  run (`evalO_of_evalL`); a callee trap stops it with a trap there.
* `le_close`: an `EvalO` run whose calls are answered by `close wasmOpen` is a
  logged run whose log `Shape.Subst` resolves (`evalL_of_evalO`). At a
  trapping callee, the logged run takes the exception answer, which stops the
  caller at once, and `Subst.intTrap` turns it into the trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Closing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Proofs.Wasm.Abstract.Recursion (funcs_of_func? closedCall_eq_bodyCall)

variable {H : Type}

/-! ## Call logs against a closed module -/

/-- The recorded call returned with its answer, as `c` allows. -/
def Ret (c : (wasmOShape H).ClosedMod) (z : OCall H) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ ([], .ret b s₂) ∈ c a s₁ args

/-- The recorded call traps in `c`. -/
def Traps (c : (wasmOShape H).ClosedMod) (z : OCall H) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ ([], .trap) ∈ c a s₁ args

/-- The recorded call diverges in `c`. -/
def Divs (c : (wasmOShape H).ClosedMod) (z : OCall H) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ ([], .div) ∈ c a s₁ args

/-- Every recorded call returned. -/
def AllRet (c : (wasmOShape H).ClosedMod) (l : List (OCall H)) : Prop := ∀ z ∈ l, Ret c z

/-- Some recorded call traps, all calls before it returned. -/
inductive TrapAt (c : (wasmOShape H).ClosedMod) : List (OCall H) → Prop
  | here {z : OCall H} {v : List (OCall H)} : Traps c z → TrapAt c (z :: v)
  | there {z : OCall H} {v : List (OCall H)} : Ret c z → TrapAt c v → TrapAt c (z :: v)

theorem OCall.eq_mk (z : OCall H) : ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ := by
  match z with
  | ⟨.inr ⟨a, args, s₁⟩, (b, s₂)⟩ => exact ⟨a, args, s₁, b, s₂, rfl⟩
  | ⟨.inl m, _⟩ => exact (m : PEmpty).elim

theorem OCall.mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' : Store H}
    {b b' : List Val ⊕ Nat} {s₂ s₂' : Store H}
    (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' ∧ b = b' ∧ s₂ = s₂' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nil_of_empty : ∀ l : List (Call (Sig.empty.{0})), l = []
  | [] => rfl
  | ⟨m, _⟩ :: _ => PEmpty.elim m

theorem allRet_nil (c : (wasmOShape H).ClosedMod) : AllRet c [] := fun _ h => nomatch h

theorem allRet_append {c : (wasmOShape H).ClosedMod} {u v : List (OCall H)} :
    AllRet c (u ++ v) ↔ AllRet c u ∧ AllRet c v := List.forall_mem_append

theorem allRet_cons {c : (wasmOShape H).ClosedMod} {z : OCall H} {v : List (OCall H)} :
    AllRet c (z :: v) ↔ Ret c z ∧ AllRet c v := List.forall_mem_cons

theorem trapAt_append_left {c : (wasmOShape H).ClosedMod} {u : List (OCall H)} (h : TrapAt c u)
    (v : List (OCall H)) : TrapAt c (u ++ v) := by
  induction h with
  | here h => exact .here h
  | there h _ ih => exact .there h ih

theorem trapAt_append_right {c : (wasmOShape H).ClosedMod} {u v : List (OCall H)}
    (hu : AllRet c u) (hv : TrapAt c v) : TrapAt c (u ++ v) := by
  induction u with
  | nil => exact hv
  | cons z u ih =>
    rw [allRet_cons] at hu
    exact .there hu.1 (ih hu.2)

theorem trapAt_append {c : (wasmOShape H).ClosedMod} {u v : List (OCall H)}
    (h : TrapAt c (u ++ v)) : TrapAt c u ∨ (AllRet c u ∧ TrapAt c v) := by
  induction u with
  | nil => exact .inr ⟨allRet_nil c, h⟩
  | cons z u ih =>
    cases h with
    | here h => exact .inl (.here h)
    | there hz h =>
      rcases ih h with h | ⟨hu, hv⟩
      · exact .inl (.there hz h)
      · exact .inr ⟨allRet_cons.2 ⟨hz, hu⟩, hv⟩

theorem trapAt_nil {c : (wasmOShape H).ClosedMod} : ¬ TrapAt c [] := nofun

/-- Resolving a log whose calls all return. -/
theorem subst_of_allRet {c : (wasmOShape H).ClosedMod} {e : End (wasmOShape H).S (List Val ⊕ Nat)} :
    ∀ {l : List (OCall H)}, AllRet c l → Shape.Subst c l e ([], e)
  | [], _ => .nil e
  | z :: l, h => by
    rw [allRet_cons] at h
    obtain ⟨⟨a, args, s₁, b, s₂, rfl, hz⟩, hl⟩ := h
    exact Shape.Subst.int hz (subst_of_allRet hl)

/-- Resolving a log with a trapping call. -/
theorem subst_of_trapAt {c : (wasmOShape H).ClosedMod} {e : End (wasmOShape H).S (List Val ⊕ Nat)}
    {l : List (OCall H)} (h : TrapAt c l) : Shape.Subst c l e ([], .trap) := by
  induction h with
  | here h =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hz⟩ := h
    exact Shape.Subst.intTrap hz
  | there h _ ih =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hz⟩ := h
    exact Shape.Subst.int hz ih

/-- What resolving a log can give. -/
theorem subst_cases {c : (wasmOShape H).ClosedMod} {e : End (wasmOShape H).S (List Val ⊕ Nat)}
    {l : List (OCall H)} {y : CallBeh (wasmOShape H).E (wasmOShape H).S (List Val ⊕ Nat)}
    (h : Shape.Subst c l e y) :
    (AllRet c l ∧ y = ([], e)) ∨ (TrapAt c l ∧ y = ([], .trap)) ∨
      (y = ([], .div) ∧ ∃ z ∈ l, Divs c z) := by
  induction h with
  | nil e => exact .inl ⟨allRet_nil c, rfl⟩
  | @ext m => exact PEmpty.elim m
  | @int g a s b s' rest e c₁ y hc _ ih =>
    obtain rfl := nil_of_empty c₁
    have hr : Ret c (OCall.mk g a s b s') := ⟨g, a, s, b, s', rfl, hc⟩
    rcases ih with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ | ⟨rfl, z, hz, h₁⟩
    · exact .inl ⟨allRet_cons.2 ⟨hr, h₁⟩, rfl⟩
    · exact .inr (.inl ⟨.there hr h₁, rfl⟩)
    · exact .inr (.inr ⟨rfl, z, List.mem_cons_of_mem _ hz, h₁⟩)
  | @intTrap g a s ans rest e c₁ hc =>
    obtain rfl := nil_of_empty c₁
    exact .inr (.inl ⟨.here ⟨g, a, s, ans.1, ans.2, rfl, hc⟩, rfl⟩)
  | @intDiv g a s ans rest e c₁ hc =>
    obtain rfl := nil_of_empty c₁
    exact .inr (.inr ⟨rfl, _, List.mem_cons_self, g, a, s, ans.1, ans.2, rfl, hc⟩)

/-! ## Exit flows -/

theorem exitFlow_eq_trap {n : Nat} {bfl : Flow} (h : exitFlow n bfl = some .trap) : bfl = .trap := by
  rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> simp_all [exitFlow]

theorem endOfFlow_ne_div (fl : Flow) (s : Store H) : endOfFlow fl s ≠ .div := by
  rcases fl <;> simp [endOfFlow]

theorem endOfFlow_eq_trap {fl : Flow} {s : Store H} (h : endOfFlow fl s = .trap) : fl = .trap := by
  rcases fl <;> simp_all [endOfFlow]

/-! ## Closed calls as a closed module -/

/-- A call relation read as a closed module through exit flows. -/
def toClosed (C : CallRel H) : (wasmOShape H).ClosedMod := fun a s vs =>
  {y | ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s' : Store H) (bfl fl : Flow),
    s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    C s a vs (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧ y = ([], endOfFlow fl s')}

theorem ret_inl {C : CallRel H} {a : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val}
    {fi : FuncInst H} {ps rs : List Validation.CValType}
    (h : Ret (toClosed C) (OCall.mk a args s₁ (.inl ws) s₂)) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    ∃ bfl vs, C s₁ a args (s₂, bfl) ∧ bfl.retVals = some vs ∧ ws.reverse = vs.take rs.length := by
  obtain ⟨a', args', s₁', b, s₂', heq, fi', ps', rs', s', bfl, fl, hfi', hty', hC, hx, hy⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | x <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, Prod.mk.injEq, End.ret.injEq, Sum.inl.injEq, reduceCtorEq, true_and,
      false_and, and_false] at hy
  all_goals obtain ⟨rfl, rfl⟩ := hy
  all_goals exact ⟨_, w, hC, rfl, by simp⟩

theorem ret_inr {C : CallRel H} {a : Nat} {args : List Val} {s₁ s₂ : Store H} {t : Nat}
    (h : Ret (toClosed C) (OCall.mk a args s₁ (.inr t) s₂)) : C s₁ a args (s₂, .throw t) := by
  obtain ⟨a', args', s₁', b, s₂', heq, fi', ps', rs', s', bfl, fl, hfi', hty', hC, hx, hy⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | x <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, Prod.mk.injEq, End.ret.injEq, Sum.inr.injEq, reduceCtorEq, true_and,
      false_and, and_false] at hy
  obtain ⟨rfl, rfl⟩ := hy
  exact hC

theorem traps_toClosed {C : CallRel H} {a : Nat} {args : List Val} {s₁ s₂ : Store H}
    {b : List Val ⊕ Nat} (h : Traps (toClosed C) (OCall.mk a args s₁ b s₂)) :
    ∃ s', C s₁ a args (s', .trap) := by
  obtain ⟨a', args', s₁', b', s₂', heq, fi', ps', rs', s', bfl, fl, _, _, hC, hx, hy⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  obtain rfl := endOfFlow_eq_trap (Prod.mk.inj hy).2.symm
  obtain rfl := exitFlow_eq_trap hx
  exact ⟨s', hC⟩

/-! ## Logged runs answered by a call relation -/

/-- A logged run whose calls all return in `toClosed C` is an `EvalO C` run; one
with a trapping call is an `EvalO C` run that traps. -/
theorem evalO_of_evalL {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {l : List (OCall H)} {r : Store H × Frame × Flow}
    (h : EvalL s f stk es l r) :
    (AllRet (toClosed C) l → EvalO C s f stk es r) ∧
      (TrapAt (toClosed C) l → ∃ s' f', EvalO C s f stk es (s', f', .trap)) := by
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

theorem close_le : Shape.close (wasmOpen (H := H)) ≤ toClosed closedCall := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, hE, hx, he⟩, hS⟩
  have close : ∀ {s'' f'' bfl'}, EvalO closedCall s (Frame.forCall fi.module vs fn.locals) []
      (liftInstrs fn.body) (s'', f'', bfl') → closedCall s a vs (s'', bfl') := fun d => by
    rw [closedCall_eq_bodyCall]
    exact ⟨fi, fn, ps, rs, _, hfi, hc, hty, d⟩
  rcases subst_cases hS with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨rfl, z, -, hz⟩
  · exact ⟨fi, ps, rs, s', bfl, fl, hfi, hty, close ((evalO_of_evalL hE).1 h), hx, by rw [he]⟩
  · obtain ⟨s'', f'', d⟩ := (evalO_of_evalL hE).2 h
    exact ⟨fi, ps, rs, s'', .trap, .trap, hfi, hty, close d, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, -, _, _, _, _, _, _, -, -, -, -, hy⟩ := hz
    exact absurd (Prod.mk.inj hy).2.symm (endOfFlow_ne_div _ _)

/-! ## `EvalO` runs answered by a closed module -/

/-- A call relation answered by a closed module through exit flows. -/
def ofClosed (c : (wasmOShape H).ClosedMod) : CallRel H := fun s a vs out =>
  ∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl : Flow),
    s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    exitFlow rs.length out.2 = some fl → ([], endOfFlow fl out.1) ∈ c a s vs

/-- How a logged run reproduces an `EvalO` run: with every call returning and
the same result, or, when the `EvalO` run trapped at a trapping callee, with
an exception there instead. -/
def Mirrors (c : (wasmOShape H).ClosedMod) (r : Store H × Frame × Flow) (l : List (OCall H))
    (r' : Store H × Frame × Flow) : Prop :=
  (AllRet c l ∧ r' = r) ∨ (r.2.2 = .trap ∧ TrapAt c l ∧ ∃ t, r'.2.2 = .throw t)

theorem Mirrors.normal {c : (wasmOShape H).ClosedMod} {r r' : Store H × Frame × Flow}
    {l : List (OCall H)} (h : Mirrors c r l r') (hr : r.2.2 ≠ .trap) : AllRet c l ∧ r' = r :=
  h.resolve_right fun h' => hr h'.1

theorem Mirrors.append {c : (wasmOShape H).ClosedMod} {r r' : Store H × Frame × Flow}
    {u l : List (OCall H)} (hu : AllRet c u) (h : Mirrors c r l r') : Mirrors c r (u ++ l) r' := by
  rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, h₃⟩
  · exact .inl ⟨allRet_append.2 ⟨hu, h⟩, rfl⟩
  · exact .inr ⟨h₁, trapAt_append_right hu h₂, h₃⟩

theorem ret_ofClosed_inl {c : (wasmOShape H).ClosedMod} {s₁ s₂ : Store H} {a : Nat}
    {args : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
    {vs : List Val} (hC : ofClosed c s₁ a args (s₂, fl)) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hvs : fl.retVals = some vs) :
    Ret c (OCall.mk a args s₁ (.inl (vs.take rs.length).reverse) s₂) := by
  refine ⟨a, args, s₁, _, s₂, rfl, hC fi ps rs (.normal (vs.take rs.length).reverse) hfi hty ?_⟩
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | x <;> simp_all [Flow.retVals, exitFlow]

/-- An `EvalO` run whose calls are answered by `ofClosed c` is mirrored by a
logged run. -/
theorem evalL_of_evalO {c : (wasmOShape H).ClosedMod} {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : EvalO (ofClosed c) s f stk es r) :
    ∃ l r', EvalL s f stk es l r' ∧ Mirrors c r l r' := by
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
    have d := EvalL.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁ hfi hty
      (by rw [List.reverse_reverse]; exact d₂)
    refine ⟨_, _, d, ?_⟩
    rw [← List.singleton_append, ← List.append_assoc]
    exact Mirrors.append (allRet_append.2 ⟨h₁, allRet_cons.2 ⟨hz, allRet_nil c⟩⟩) h₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    have hz : Traps c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr 0) s₂) :=
      ⟨_, _, _, _, _, rfl, hcall fi ps rs .trap (funcs_of_func? hfi) hty rfl⟩
    exact ⟨_, _, EvalL.callThrow (t := 0) (s₂ := s₂) d₁ hfi hty,
      .inr ⟨rfl, trapAt_append_right h₁ (.here hz), 0, rfl⟩⟩
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih =>
    obtain ⟨l₁, r₁, d₁, m₁⟩ := ih
    obtain ⟨h₁, rfl⟩ := m₁.normal nofun
    have hz : Ret c (OCall.mk a (stk₁.take ps.length).reverse s₁ (.inr t) s₂) :=
      ⟨_, _, _, _, _, rfl, hcall fi ps rs (.throw t) (funcs_of_func? hfi) hty rfl⟩
    exact ⟨_, _, EvalL.callThrow (t := t) (s₂ := s₂) d₁ hfi hty,
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

theorem closedCall_le_ofClosed : (closedCall : CallRel H) ≤ ofClosed (Shape.close wasmOpen) := by
  refine OrderHom.lfp_le _ ?_
  rintro s a vs ⟨s', bfl⟩ ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩ fi' ps' rs' fl hfi' hty' hx
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  rw [Shape.close, ← OrderHom.map_lfp]
  obtain ⟨l, r', dL, h⟩ := evalL_of_evalO d
  rcases h with ⟨h, rfl⟩ | ⟨h₁, h₂, t, h₃⟩
  · exact ⟨(l, endOfFlow fl s'), ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hc, hty, dL, hx, rfl⟩,
      subst_of_allRet h⟩
  · obtain ⟨s'', f'', fl'⟩ := r'
    obtain rfl : bfl = .trap := h₁
    obtain rfl : fl = .trap := by simpa [exitFlow] using hx.symm
    subst h₃
    exact ⟨(l, endOfFlow (.throw t) s''), ⟨fi, fn, ps, rs, s'', f'', .throw t, .throw t, hfi, hc,
      hty, dL, rfl, rfl⟩, subst_of_trapAt h₂⟩

theorem le_close : toClosed closedCall ≤ Shape.close (wasmOpen (H := H)) := by
  rintro a s vs y ⟨fi, ps, rs, s', bfl, fl, hfi, hty, hC, hx, rfl⟩
  exact closedCall_le_ofClosed _ _ _ _ hC fi ps rs fl hfi hty hx

theorem close_eq : Shape.close (wasmOpen (H := H)) = toClosed closedCall :=
  le_antisymm close_le le_close

/-- **Closing the open module gives the closed outcomes.** -/
theorem close_wasmOpen (a : Nat) (s : Store H) (vs : List Val) :
    Shape.close wasmOpen a s vs =
      {y | ∃ s' fl, ClosedOutcome s a vs s' fl ∧ y = ([], endOfFlow fl s')} := by
  rw [close_eq]
  ext y
  constructor
  · rintro ⟨fi, ps, rs, s', bfl, fl, hfi, hty, hC, hx, rfl⟩
    rw [closedCall_eq_bodyCall] at hC
    obtain ⟨fi', fn, ps', rs', f₂, hfi', hc, hty', d⟩ := hC
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    exact ⟨s', fl, ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩, rfl⟩
  · rintro ⟨s', fl, ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩, rfl⟩
    refine ⟨fi, ps, rs, s', bfl, fl, hfi, hty, ?_, hx, rfl⟩
    rw [closedCall_eq_bodyCall]
    exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩

end Silmaril.Proofs.Wasm.Abstract.Closing
