module

public import Silmaril.Wasm.Interp.ExampleTailEH.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms

/-!
# Tail calls inside handlers (proofs)

The answers of the closure with pending tail calls (`XRecursionP.closedCallXP`) for the four
functions of `ExampleTailEH`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Interp.ExampleTailEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Interp.ExampleTailEH

theorem tTag_expand : ∃ ts : Validation.Ty (.list .val),
    Validation.Expand tTag.type (.func ts .nil) ∧ ts.length = 1 :=
  ⟨_, Validation.Expand.iff.mpr rfl, rfl⟩

/-- `$thrower`'s body throws the exception `0` with the field `9`. -/
theorem thrower_body : EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) []
    (liftInstrs thrower.body) (tStore', Frame.forCall tMod [] [], .flow (.throw 0)) := by
  obtain ⟨ts, he, hn⟩ := tTag_expand
  have h := EvalOXP.throw (C := closedCallXP) (s := tStore) (f := Frame.forCall tMod [] [])
    (stk := [v9]) (x := ⟨0⟩) (ta := 0) (ti := tTag) (es := []) .nil (by rfl) he (by simp [hn])
  simp only [hn] at h
  exact .opOk (fun _ h => by cases h) .nil rfl h

/-- **`$thrower` throws.** -/
theorem thrower_answer : closedCallXP tStore 0 [] (tStore', .throw 0) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, thrower, [], _, _, _, _, rfl, rfl, rfl, thrower_body, .flow⟩

/-- `$tailer`'s body ends in the pending tail call of `$thrower`: it passes the handler and the
block untouched. -/
theorem tailer_body : EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) []
    (liftInstrs tailer.body) (tStore, Frame.forCall tMod [] [], .tail 0 [] 1) :=
  .blockEsc (np := 0) (nr := 1) rfl
    (.tryEsc (np := 0) (nr := 0) rfl
      (.tail (ps := []) (rs := [.num (.int .i32)]) .nil (.direct rfl) rfl rfl
        (fun _ h => by cases h)) trivial trivial)
    trivial

/-- **`$tailer` throws `$thrower`'s exception**: the tail call is answered only when `$tailer`'s
frame is left, outside its handler. -/
theorem tailer_answer : closedCallXP tStore 1 [] (tStore', .throw 0) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, tailer, [], _, _, _, _, rfl, rfl, rfl, tailer_body,
    .tail (n := 1) thrower_answer (.inr trivial)⟩

/-- `$caller`'s body: the ordinary call throws inside the handler, which catches the exception;
the block produces `9`. -/
theorem caller_body : EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) []
    (liftInstrs caller.body) (tStore', Frame.forCall tMod [] [], .flow (.normal [v9])) :=
  .blockOk (np := 0) (nr := 1) rfl
    (.tryCatch (np := 0) (nr := 0) rfl
      (.callThrow (ps := []) (rs := [.num (.int .i32)]) .nil rfl rfl thrower_answer)
      (.catch_ (e := ⟨0, [v9]⟩) rfl rfl))
    rfl .nil

/-- **`$caller` returns `9`**: the ordinary call's exception is caught. -/
theorem caller_answer : closedCallXP tStore 2 [] (tStore', .normal [v9]) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, caller, [], _, _, _, _, rfl, rfl, rfl, caller_body, .flow⟩

/-- `$nuller`'s body: the tail call of null traps, through the handler and the block. -/
theorem nuller_body : EvalOXP closedCallXP tStore (Frame.forCall tMod [] nuller.locals) []
    (liftInstrs nuller.body) (tStore, Frame.forCall tMod [] nuller.locals, .flow .trap) :=
  .blockEsc (np := 0) (nr := 1) rfl
    (.tryEsc (np := 0) (nr := 0) rfl
      (.opOk (fun _ h => by cases h) .nil rfl (.tailRes .nil .refNull)) trivial trivial)
    trivial

/-- **`$nuller` traps.** -/
theorem nuller_answer : closedCallXP tStore 3 [] (tStore, .trap) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, nuller, [], _, _, _, _, rfl, rfl, rfl, nuller_body, .flow⟩

/-! ## The answers are unique: the handler is bypassed, or catches -/

/-- The only run of `throw $t` on `[9]`. -/
theorem throw_inv {f : Frame} (hf : f.module = tMod) {r : Store Empty × Frame × POut}
    (h : EvalOXP closedCallXP tStore f [v9] [.op (.throw ⟨0⟩) []] r) :
    r = (tStore', f, .flow (.throw 0)) := by
  cases h with
  | argsAbort hargs ho => cases hargs; exact absurd trivial ho
  | opOk hi hargs hflat => cases hargs; simp [evalFlat] at hflat
  | opStop hi hargs hflat => cases hargs; simp [evalFlat] at hflat
  | tail _ hres => cases hres
  | tailRes _ hres => cases hres
  | throw hargs ht he hn =>
    cases hargs
    have ht' : tStore.tag? f ⟨0⟩ = some (0, tTag) := by simp only [Store.tag?, hf]; rfl
    rw [ht'] at ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht)
    obtain ⟨ts', he', hn'⟩ := tTag_expand
    have h12 := (Validation.Expand.iff.mp he).symm.trans (Validation.Expand.iff.mp he')
    simp only [Option.some.injEq] at h12
    cases h12
    simp only [hn']
    rfl

/-- **`$thrower`'s only answer is its exception.** -/
theorem thrower_answer_inv {out : Store Empty × Flow} (h : closedCallXP tStore 0 [] out) :
    out = (tStore', .throw 0) := by
  rw [closedCallXP_fixpoint] at h
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩ := h
  simp only [tStore, List.getElem?_cons_zero, Option.some.injEq] at hfi
  subst hfi
  cases hcode
  cases d with
  | argsAbort hargs ho => cases hargs; exact absurd trivial ho
  | opOk hi hargs hflat hk =>
    cases hargs
    simp only [evalFlat, Option.some.injEq, Prod.mk.injEq, Flow.normal.injEq] at hflat
    obtain ⟨rfl, rfl, rfl⟩ := hflat
    have := throw_inv rfl hk
    cases this
    cases hfr
    rfl
  | opStop hi hargs hflat hfl =>
    cases hargs
    simp only [evalFlat, Option.some.injEq, Prod.mk.injEq] at hflat
    obtain ⟨-, -, rfl⟩ := hflat
    exact absurd trivial hfl
  | tail _ hres => cases hres
  | tailRes _ hres => cases hres

/-- The only run of `return_call $thrower`: the pending tail call. -/
theorem returnCall_inv {f : Frame} (hf : f.module = tMod) {es : List Binaryen.BExpr}
    {r : Store Empty × Frame × POut}
    (h : EvalOXP closedCallXP tStore f [] (.op (.returnCall ⟨0⟩) [] :: es) r) :
    r = (tStore, f, .tail 0 [] 1) := by
  cases h with
  | argsAbort hargs ho => cases hargs; exact absurd trivial ho
  | opOk hi hargs hflat => cases hargs; simp [evalFlat] at hflat
  | opStop hi hargs hflat => cases hargs; simp [evalFlat] at hflat
  | tail hargs hres hfi hty =>
    cases hargs
    cases hres with
    | direct hfi' =>
      have : tStore.func? f ⟨0⟩ = some (0, ⟨tTy, tMod, .wasm thrower⟩) := by
        simp only [Store.func?, hf]; rfl
      rw [this] at hfi'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hfi')
      simp only [tStore, List.getElem?_cons_zero, Option.some.injEq] at hfi
      subst hfi
      have : Validation.DefType.funcType? tTy = some ([], [.num (.int .i32)]) := rfl
      rw [this] at hty
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty)
      rfl
  | tailRes hargs hres => cases hargs; cases hres

/-- **`$tailer`'s only answer is `$thrower`'s exception: the handler is bypassed.** -/
theorem tailer_answer_inv {out : Store Empty × Flow} (h : closedCallXP tStore 1 [] out) :
    out = (tStore', .throw 0) := by
  rw [closedCallXP_fixpoint] at h
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩ := h
  simp only [tStore, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hfi
  subst hfi
  cases hcode
  have key : ∀ {r : Store Empty × Frame × POut},
      EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) []
        [.tryTable .empty [.catch_ ⟨0⟩ ⟨0⟩] [.op (.returnCall ⟨0⟩) []], .op .unreachable []] r →
      r = (tStore, Frame.forCall tMod [] [], .tail 0 [] 1) := by
    intro r h
    cases h with
    | tryOk har hbody => simp only [List.take_nil] at hbody; cases returnCall_inv rfl hbody
    | tryBrk har hbody => simp only [List.take_nil] at hbody; cases returnCall_inv rfl hbody
    | tryEsc har hbody => simp only [List.take_nil] at hbody; exact returnCall_inv rfl hbody
    | tryCatch har hbody => simp only [List.take_nil] at hbody; cases returnCall_inv rfl hbody
    | tryRethrow har hbody => simp only [List.take_nil] at hbody; cases returnCall_inv rfl hbody
  cases d with
  | blockOk har hbody =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq, reduceCtorEq, and_false] at e
  | blockBrk har hbody =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq, reduceCtorEq, and_false] at e
  | blockEsc har hbody =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    cases hfr with
    | tail hcall hfl =>
      have e₂ := thrower_answer_inv hcall
      simp only [Prod.mk.injEq] at e₂
      obtain ⟨rfl, rfl⟩ := e₂
      rfl

/-- **`$caller`'s only answer is `9`: the ordinary call's exception is caught.** -/
theorem caller_answer_inv {out : Store Empty × Flow} (h : closedCallXP tStore 2 [] out) :
    out = (tStore', .normal [v9]) := by
  rw [closedCallXP_fixpoint] at h
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩ := h
  simp only [tStore, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hfi
  subst hfi
  cases hcode
  have hcall_inv : ∀ {es : List Binaryen.BExpr} {r : Store Empty × Frame × POut},
      EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) [] (.op (.call ⟨0⟩) [] :: es) r →
      r = (tStore', Frame.forCall tMod [] [], .flow (.throw 0)) := by
    intro es r h
    have hfx : tStore.func? (Frame.forCall tMod [] []) ⟨0⟩ =
        some (0, ⟨tTy, tMod, .wasm thrower⟩) := by
      simp only [Store.func?, Frame.forCall]; rfl
    cases h with
    | argsAbort hargs ho => cases hargs; exact absurd trivial ho
    | tail _ hres => cases hres
    | tailRes _ hres => cases hres
    | callOk hargs hfi hty hcall hvs =>
      cases hargs; rw [hfx] at hfi; cases hfi
      simp only [List.take_nil, List.reverse_nil] at hcall
      have e := thrower_answer_inv hcall
      simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; simp [Flow.retVals] at hvs
    | callTrap hargs hfi hty hcall =>
      cases hargs; rw [hfx] at hfi; cases hfi
      simp only [List.take_nil, List.reverse_nil] at hcall
      have e := thrower_answer_inv hcall
      simp only [Prod.mk.injEq, reduceCtorEq, and_false] at e
    | callThrow hargs hfi hty hcall =>
      cases hargs; rw [hfx] at hfi; cases hfi
      simp only [List.take_nil, List.reverse_nil] at hcall
      have e := thrower_answer_inv hcall
      simp only [Prod.mk.injEq, Flow.throw.injEq] at e; obtain ⟨rfl, rfl⟩ := e; rfl
    | opOk hi => exact absurd rfl (hi _)
    | opStop hi => exact absurd rfl (hi _)
  have key : ∀ {r : Store Empty × Frame × POut},
      EvalOXP closedCallXP tStore (Frame.forCall tMod [] []) []
        [.tryTable .empty [.catch_ ⟨0⟩ ⟨0⟩] [.op (.call ⟨0⟩) []], .op .unreachable []] r →
      r = (tStore', Frame.forCall tMod [] [], .flow (.brk 0 [v9])) := by
    intro r h
    cases h with
    | tryOk har hbody hvs =>
      simp only [List.take_nil] at hbody
      have e := hcall_inv hbody
      simp only [Prod.mk.injEq, POut.flow.injEq] at e
      obtain ⟨-, -, rfl⟩ := e
      simp [Flow.blockVals] at hvs
    | tryBrk har hbody =>
      simp only [List.take_nil] at hbody
      have e := hcall_inv hbody
      simp only [Prod.mk.injEq, POut.flow.injEq, reduceCtorEq, and_false] at e
    | tryEsc har hbody ho hnt =>
      simp only [List.take_nil] at hbody
      have e := hcall_inv hbody
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, -, rfl⟩ := e
      exact hnt.elim
    | tryCatch har hbody hc =>
      simp only [List.take_nil] at hbody
      have e := hcall_inv hbody
      simp only [Prod.mk.injEq, POut.flow.injEq, Flow.throw.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      cases hc with
      | catch_ he ht =>
        simp only [tStore', tStore, Store.addExn, List.nil_append, List.getElem?_cons_zero,
          Option.some.injEq] at he
        subst he
        simp only [List.drop_nil, List.append_nil]
        rfl
      | next hm => exact absurd ⟨_, 0, rfl, rfl, rfl⟩ hm
    | tryRethrow har hbody hc =>
      simp only [List.take_nil] at hbody
      have e := hcall_inv hbody
      simp only [Prod.mk.injEq, POut.flow.injEq, Flow.throw.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      cases hc with
      | next hm => exact absurd ⟨_, 0, rfl, rfl, rfl⟩ hm
  cases d with
  | blockOk har hbody hvs hk =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq, POut.flow.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    simp only [Flow.blockVals, Option.some.injEq] at hvs
    subst hvs
    simp only [Binaryen.arity, Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    cases hk
    cases hfr
    rfl
  | blockBrk har hbody =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq, POut.flow.injEq, Flow.brk.injEq] at e
    omega
  | blockEsc har hbody ho =>
    have e := key (by simp only [List.take_nil] at hbody; exact hbody)
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, -, rfl⟩ := e
    exact ho.elim

end Silmaril.Proofs.Wasm.Interp.ExampleTailEH
