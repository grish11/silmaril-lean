module

public import Silmaril.Proofs.Wasm.Abstract.HostClosing.Log
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Replaying a logged closed behaviour against a host (proofs)

`close_le_toClosedH`: a behaviour of `Shape.close wasmHOpen` whose host answers the host
relation allows (`HostRel.Consistent`) is an outcome of `hostCall host`, read through exit
flows. Least-fixpoint induction: a Wasm callee's logged run, its calls answered by consistent
closed behaviours, is an `EvalO (hostCall host)` run (`evalO_of_evalLH`); a host callee's
single import call, answered consistently, is a `hostAns` answer.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

/-- The host answers of a log are allowed. -/
abbrev Cons (host : HostSemantics H) (q : List (ICall H)) : Prop :=
  (coreHostRel host).Consistent q

theorem cons_append {q₁ q₂ : List (ICall H)} : Cons host (q₁ ++ q₂) ↔ Cons host q₁ ∧ Cons host q₂ :=
  List.forall_mem_append

theorem exitFlow_eq_trap {n : Nat} {bfl : Flow} (h : exitFlow n bfl = some .trap) : bfl = .trap := by
  rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> simp_all [exitFlow]

theorem endOfFlow_ne_div (fl : Flow) (s : Store H) : endOfFlow fl s ≠ .div := by
  rcases fl <;> simp [endOfFlow]

theorem endOfFlow_eq_trap {fl : Flow} {s : Store H} (h : endOfFlow fl s = .trap) : fl = .trap := by
  rcases fl <;> simp_all [endOfFlow]

/-- `hostCall host` read as a closed module of `wasmHShape`: a behaviour whose host answers
are allowed is a `hostCall` outcome through the exit flow. -/
def toClosedH (host : HostSemantics H) : (wasmHShape H).ClosedMod := fun a s vs =>
  {y | Cons host y.1 → ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s' : Store H)
    (bfl fl : Flow), s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    hostCall host s a vs (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧ y.2 = endOfFlow fl s'}

theorem ret_inlH {a : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val} {q : List (ICall H)}
    {fi : FuncInst H} {ps rs : List Validation.CValType}
    (h : RetL (toClosedH host) (OCall.mk a args s₁ (.inl ws) s₂) q) (hq : Cons host q)
    (hfi : s₁.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    ∃ bfl vs, hostCall host s₁ a args (s₂, bfl) ∧ bfl.retVals = some vs ∧
      ws.reverse = vs.take rs.length := by
  obtain ⟨a', args', s₁', b, s₂', heq, hm⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  obtain ⟨fi', ps', rs', s', bfl, fl, hfi', hty', hC, hx, hy⟩ := hm hq
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | x <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inl.injEq, reduceCtorEq, false_and] at hy
  all_goals obtain ⟨rfl, rfl⟩ := hy
  all_goals exact ⟨_, w, hC, rfl, by simp⟩

theorem ret_inrH {a : Nat} {args : List Val} {s₁ s₂ : Store H} {t : Nat} {q : List (ICall H)}
    (h : RetL (toClosedH host) (OCall.mk a args s₁ (.inr t) s₂) q) (hq : Cons host q) :
    hostCall host s₁ a args (s₂, .throw t) := by
  obtain ⟨a', args', s₁', b, s₂', heq, hm⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  obtain ⟨fi', ps', rs', s', bfl, fl, -, -, hC, hx, hy⟩ := hm hq
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | x <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inr.injEq, reduceCtorEq, false_and] at hy
  obtain ⟨rfl, rfl⟩ := hy
  exact hC

theorem trapsH {a : Nat} {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    {q : List (ICall H)} (h : TrapsL (toClosedH host) (OCall.mk a args s₁ b s₂) q)
    (hq : Cons host q) : ∃ s', hostCall host s₁ a args (s', .trap) := by
  obtain ⟨a', args', s₁', b', s₂', heq, hm⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := OCall.mk_inj heq
  obtain ⟨fi', ps', rs', s', bfl, fl, -, -, hC, hx, hy⟩ := hm hq
  obtain rfl := endOfFlow_eq_trap hy.symm
  obtain rfl := exitFlow_eq_trap hx
  exact ⟨s', hC⟩

theorem toClosedH_ne_div {a : Nat} {s : Store H} {vs : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : y ∈ toClosedH host a s vs)
    (hq : Cons host y.1) : y.2 ≠ .div := by
  obtain ⟨_, _, _, _, _, fl, _, _, _, _, e⟩ := hy hq
  rw [e]
  exact endOfFlow_ne_div fl _

theorem divsH {z : OCall H} {q : List (ICall H)} (h : DivsL (toClosedH host) z q)
    (hq : Cons host q) : False := by
  obtain ⟨a, args, s₁, b, s₂, -, hm⟩ := h
  exact toClosedH_ne_div (y := (q, .div)) hm hq rfl

/-- The calls of a logged run returning consistently in `toClosedH host` give an
`EvalO (hostCall host)` run; a trapping call gives a trapping one. -/
theorem evalO_of_evalLH {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (h : EvalL s f stk es l r) :
    (∀ q, AllRetL (toClosedH host) l q → Cons host q → EvalO (hostCall host) s f stk es r) ∧
      (∀ q, TrapAtL (toClosedH host) l q → Cons host q →
        ∃ s' f', EvalO (hostCall host) s f stk es (s', f', .trap)) := by
  induction h with
  | nil => exact ⟨fun _ _ _ => .nil, fun _ h => absurd h trapAtL_nil⟩
  | argsAbort _ hfl ih =>
    exact ⟨fun q h hq => .argsAbort (ih.1 q h hq) hfl, fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | callRet _ hfi hty _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      cases h₂ with
      | cons hz h₃ =>
        rw [cons_append, cons_append] at hq
        obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inlH hz hq.2.1 (funcs_of_func? hfi) hty
        exact .callOk (ih₁.1 _ h₁ hq.1) hfi hty hC hvs (hws ▸ ih₂.1 _ h₃ hq.2.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        cases h with
        | here h =>
          obtain ⟨s', hC⟩ := trapsH h hq.2
          exact ⟨s', _, .callTrap (ih₁.1 _ hu hq.1) hfi hty hC⟩
        | there hz h =>
          rw [cons_append] at hq
          obtain ⟨bfl, vs, hC, hvs, hws⟩ := ret_inlH hz hq.2.1 (funcs_of_func? hfi) hty
          obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2.2
          exact ⟨s', f', .callOk (ih₁.1 _ hu hq.1) hfi hty hC hvs (hws ▸ d)⟩
  | callThrow _ hfi hty ih =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      cases h₂ with
      | cons hz h₃ =>
        rw [cons_append, cons_append] at hq
        exact .callThrow (ih.1 _ h₁ hq.1) hfi hty (ret_inrH hz hq.2.1)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih.2 q h hq
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        cases h with
        | here h =>
          obtain ⟨s', hC⟩ := trapsH h hq.2
          exact ⟨s', _, .callTrap (ih.1 _ hu hq.1) hfi hty hC⟩
        | there _ h => exact absurd h trapAtL_nil
  | opOk hi _ hflat _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .opOk hi (ih₁.1 _ h₁ hq.1) hflat (ih₂.1 _ h₂ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .argsAbort d Flow.notNormal_trap⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .opOk hi (ih₁.1 _ hu hq.1) hflat d⟩
  | opStop hi _ hflat hfl ih =>
    exact ⟨fun q h hq => .opStop hi (ih.1 q h hq) hflat hfl, fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .argsAbort d Flow.notNormal_trap⟩⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .blockOk har (ih₁.1 _ h₁ hq.1) hvs (ih₂.1 _ h₂ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .blockEsc har d trivial⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .blockOk har (ih₁.1 _ hu hq.1) hvs d⟩
  | blockBrk har _ ih =>
    exact ⟨fun q h hq => .blockBrk har (ih.1 q h hq), fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .blockEsc har d trivial⟩⟩
  | blockEsc har _ hfl ih =>
    exact ⟨fun q h hq => .blockEsc har (ih.1 q h hq) hfl, fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .blockEsc har d trivial⟩⟩
  | loopOk har _ _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .loopOk har (ih₁.1 _ h₁ hq.1) (ih₂.1 _ h₂ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .loopEsc har d trivial⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .loopOk har (ih₁.1 _ hu hq.1) d⟩
  | loopBack har _ _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .loopBack har (ih₁.1 _ h₁ hq.1) (ih₂.1 _ h₂ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .loopEsc har d trivial⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .loopBack har (ih₁.1 _ hu hq.1) d⟩
  | loopBrk har _ ih =>
    exact ⟨fun q h hq => .loopBrk har (ih.1 q h hq), fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .loopEsc har d trivial⟩⟩
  | loopEsc har _ hfl ih =>
    exact ⟨fun q h hq => .loopEsc har (ih.1 q h hq) hfl, fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .loopEsc har d trivial⟩⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := allRetL_append.1 h
      obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h₁₂
      rw [cons_append, cons_append] at hq
      exact .ifOk (ih₁.1 _ h₁ hq.1.1) hb har (ih₂.1 _ h₂ hq.1.2) hvs (ih₃.1 _ h₃ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁₂, q₃, hqe, hu, h⟩
      · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu', h⟩
        · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
          exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
        · rw [hqe] at hq
          rw [cons_append] at hq
          obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
          exact ⟨s', f', .ifEsc (ih₁.1 _ hu' hq.1) hb har d trivial⟩
      · rw [hqe] at hq
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 hu
        rw [cons_append, cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₃.2 _ h hq.2
        exact ⟨s', f', .ifOk (ih₁.1 _ h₁ hq.1.1) hb har (ih₂.1 _ h₂ hq.1.2) hvs d⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .ifBrk (ih₁.1 _ h₁ hq.1) hb har (ih₂.1 _ h₂ hq.2)
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .ifEsc (ih₁.1 _ hu hq.1) hb har d trivial⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    refine ⟨fun q h hq => ?_, fun q h hq => ?_⟩
    · obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := allRetL_append.1 h
      rw [cons_append] at hq
      exact .ifEsc (ih₁.1 _ h₁ hq.1) hb har (ih₂.1 _ h₂ hq.2) hfl
    · rcases trapAtL_append h with h | ⟨q₁, q₂, hqe, hu, h⟩
      · obtain ⟨s', f', d⟩ := ih₁.2 q h hq
        exact ⟨s', f', .ifAbort d Flow.notNormal_trap⟩
      · rw [hqe] at hq
        rw [cons_append] at hq
        obtain ⟨s', f', d⟩ := ih₂.2 _ h hq.2
        exact ⟨s', f', .ifEsc (ih₁.1 _ hu hq.1) hb har d trivial⟩
  | ifAbort _ hfl ih =>
    exact ⟨fun q h hq => .ifAbort (ih.1 q h hq) hfl, fun q h hq =>
      let ⟨s', f', d⟩ := ih.2 q h hq; ⟨s', f', .ifAbort d Flow.notNormal_trap⟩⟩

/-- **A consistent closed behaviour is a `hostCall` outcome.** -/
theorem close_le_toClosedH : Shape.close (wasmHOpen (H := H)) ≤ toClosedH host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, hx, hS⟩
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩
  · have close : ∀ {s'' f'' bfl'}, EvalO (hostCall host) s (Frame.forCall fi.module vs fn.locals)
        [] (liftInstrs fn.body) (s'', f'', bfl') → hostCall host s a vs (s'', bfl') := fun d => by
      rw [hostCall_fixpoint]
      exact .inl ⟨fi, fn, ps, rs, _, hfi, hc, hty, d⟩
    intro hq
    rcases substL_cases hS with ⟨q, h, rfl⟩ | ⟨q, h, rfl⟩ | ⟨hd, q₁, q₂, z, e, -, hz⟩
    · exact ⟨fi, ps, rs, s', bfl, fl, hfi, hty, close ((evalO_of_evalLH hE).1 q h hq), hxf, rfl⟩
    · obtain ⟨s'', f'', d⟩ := (evalO_of_evalLH hE).2 q h hq
      exact ⟨fi, ps, rs, s'', .trap, .trap, hfi, hty, close d, rfl, rfl⟩
    · rw [e, cons_append] at hq
      exact (divsH hz hq.2).elim
  · intro hq
    cases hS with
    | ext h =>
      cases h
      have hm : host hh s vs (.returned s' r) := hq _ List.mem_cons_self
      refine ⟨fi, ps, rs, s', resFlow r, fl, hfi, hty, ?_, hxf, rfl⟩
      rw [hostCall_fixpoint]
      exact .inr ⟨fi, hh, r, hfi, hc, hm, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosing
