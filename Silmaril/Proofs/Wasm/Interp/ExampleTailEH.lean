module

public import Silmaril.Wasm.Interp.ExampleTailEH.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Proofs.Wasm.Interp.PendClose
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# Tail calls inside handlers (proofs)

The answers of the closure with pending tail calls (`XRecursionP.closedCallXP`) for the four
functions of `ExampleTailEH`, on the original store and on the corrected one; the validation of
the corrected module `tModuleV` and the rejection of the original one (by the validator and by
the arity checker); and the Core 3.0 runs of the calls of the corrected store's functions, from
the soundness of the closure (`Interp.closedCallXP_sound`).
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


/-! ## Validation: the original module is rejected, the corrected one is valid -/

/-- The original module is rejected by the validator. -/
theorem tModuleOld_invalid : Validation.validate? tModuleOld = none := by decide +kernel

/-- Its `$caller` alone is ill-typed (the empty-typed `try_table` leaves an `i32`). -/
theorem tModule_caller_invalid :
    Validation.validate? (tModule [thrower, tailer, caller, nullerV]) = none := by decide +kernel

/-- Its `$nuller` alone is ill-typed (`return_call_ref $r` on a `funcref`). -/
theorem tModule_nuller_invalid :
    Validation.validate? (tModule [thrower, tailer, callerV, nuller]) = none := by decide +kernel

/-- The corrected module passes the validator. -/
theorem tModuleV_valid : (Validation.validate? tModuleV).isSome = true := by decide +kernel

/-- **The corrected module is valid.** -/
theorem tModuleV_moduleValid : Validation.ModuleValid tModuleV :=
  Validation.validate_sound tModuleV_valid

/-- **The original module is not valid** (by the completeness of the validator). -/
theorem tModuleOld_not_moduleValid : ¬ Validation.ModuleValid tModuleOld := fun h => by
  have := Validation.validate?_isSome_iff.mpr h
  rw [tModuleOld_invalid] at this
  cases this

section Check

open Silmaril.Wasm.Interp

theorem tTy_funcType : Validation.DefType.funcType? tTy = some ([], [.num (.int .i32)]) := rfl

/-- **The original store fails the arity checker**, on `$caller`. -/
theorem tStore_not_storeChk : ¬ StoreChkE (ehExt [tTag]) tStore.funcs := fun h => by
  have := h 2 _ caller [] [.num (.int .i32)] rfl rfl tTy_funcType
  revert this
  decide

/-- The corrected store has the tag invariants: its tag is `$t`, and no exception yet. -/
theorem tStoreV_tagsOk : TagsOk [tTag] tStoreV :=
  ⟨rfl, fun a e h => by simp [tStoreV] at h⟩

/-- The corrected store's four bodies pass the exception checker. -/
theorem tStoreV_storeChk : StoreChkE (ehExt [tTag]) tStoreV.funcs := by
  intro a fi fn ps rs h₁ h₂ h₃
  rcases a with _ | _ | _ | _ | a
  rotate_left 4
  · simp [tStoreV] at h₁
  all_goals simp only [tStoreV, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at h₁
  all_goals
    subst h₁
    cases h₂
    have : (ps, rs) = ([], [.num (.int .i32)]) := Option.some.inj (h₃.symm.trans rfl)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
    decide

end Check

/-! ## The closure's answers on the corrected store -/

theorem thrower_bodyV : EvalOXP closedCallXP tStoreV (Frame.forCall tMod [] []) []
    (liftInstrs thrower.body) (tStoreV', Frame.forCall tMod [] [], .flow (.throw 0)) := by
  obtain ⟨ts, he, hn⟩ := tTag_expand
  have h := EvalOXP.throw (C := closedCallXP) (s := tStoreV) (f := Frame.forCall tMod [] [])
    (stk := [v9]) (x := ⟨0⟩) (ta := 0) (ti := tTag) (es := []) .nil (by rfl) he (by simp [hn])
  simp only [hn] at h
  exact .opOk (fun _ h => by cases h) .nil rfl h

/-- `$thrower` throws, in the corrected store. -/
theorem thrower_answerV : closedCallXP tStoreV 0 [] (tStoreV', .throw 0) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, thrower, [], _, _, _, _, rfl, rfl, rfl, thrower_bodyV, .flow⟩

theorem tailer_bodyV : EvalOXP closedCallXP tStoreV (Frame.forCall tMod [] []) []
    (liftInstrs tailer.body) (tStoreV, Frame.forCall tMod [] [], .tail 0 [] 1) :=
  .blockEsc (np := 0) (nr := 1) rfl
    (.tryEsc (np := 0) (nr := 0) rfl
      (.tail (ps := []) (rs := [.num (.int .i32)]) .nil (.direct rfl) rfl rfl
        (fun _ h => by cases h)) trivial trivial)
    trivial

/-- `$tailer` throws `$thrower`'s exception, in the corrected store. -/
theorem tailer_answerV : closedCallXP tStoreV 1 [] (tStoreV', .throw 0) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, tailer, [], _, _, _, _, rfl, rfl, rfl, tailer_bodyV,
    .tail (n := 1) thrower_answerV (.inr trivial)⟩

/-- `$caller`'s body in the corrected store: the call throws inside the handler, the clause
`catch $t 0` branches to the block with the field `9` (the `try_table` has result `i32`), and the
block produces `9`. -/
theorem caller_bodyV : EvalOXP closedCallXP tStoreV (Frame.forCall tMod [] []) []
    (liftInstrs callerV.body) (tStoreV', Frame.forCall tMod [] [], .flow (.normal [v9])) :=
  .blockOk (np := 0) (nr := 1) rfl
    (.tryCatch (np := 0) (nr := 1) rfl
      (.callThrow (ps := []) (rs := [.num (.int .i32)]) .nil rfl rfl thrower_answerV)
      (.catch_ (e := ⟨0, [v9]⟩) rfl rfl))
    rfl .nil

/-- `$caller` returns `9`, in the corrected store. -/
theorem caller_answerV : closedCallXP tStoreV 2 [] (tStoreV', .normal [v9]) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, callerV, [], _, _, _, _, rfl, rfl, rfl, caller_bodyV, .flow⟩

theorem nuller_bodyV : EvalOXP closedCallXP tStoreV (Frame.forCall tMod [] nullerV.locals) []
    (liftInstrs nullerV.body) (tStoreV, Frame.forCall tMod [] nullerV.locals, .flow .trap) :=
  .blockEsc (np := 0) (nr := 1) rfl
    (.tryEsc (np := 0) (nr := 0) rfl
      (.opOk (fun _ h => by cases h) .nil rfl (.tailRes .nil .refNull)) trivial trivial)
    trivial

/-- `$nuller` traps, in the corrected store. -/
theorem nuller_answerV : closedCallXP tStoreV 3 [] (tStoreV, .trap) := by
  rw [closedCallXP_fixpoint]
  exact ⟨_, nullerV, [], _, _, _, _, rfl, rfl, rfl, nuller_bodyV, .flow⟩

/-! ## The Core runs -/

section Core

open Silmaril.Wasm.Interp

variable {P : Numerics.Profile} {host : HostSemantics Empty}

/-- **`$tailer` throws `$thrower`'s exception in Core 3.0**, called in any `call_ref` form from
any frame: its tail call leaves the handler by `return_call_ref-handler` and the frame by
`return_call_ref-frame-addr` before `$thrower` runs, so the clause `catch $t 0` never sees the
exception. -/
theorem tailer_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 1), c]⟩ ⟨tStoreV', f, throwing 0⟩ :=
  ((closedCallXP_sound (P := P) (host := host) [tTag] tStoreV 1 [] _ tailer_answerV
    tStoreV_tagsOk).2 f _ [] [.num (.int .i32)] c tStoreV_storeChk rfl tTy_funcType rfl
    hc).2.2.2 0 rfl

/-- **`$caller` returns `9` in Core 3.0**: the ordinary call throws inside the handler, which
catches the exception. -/
theorem caller_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 2), c]⟩ ⟨tStoreV', f, vals [v9]⟩ := by
  have h := ((closedCallXP_sound (P := P) (host := host) [tTag] tStoreV 2 [] _ caller_answerV
    tStoreV_tagsOk).2 f _ [] [.num (.int .i32)] c tStoreV_storeChk rfl tTy_funcType rfl hc).2.1
    [v9] rfl
  simpa using h

/-- **`$nuller` traps in Core 3.0**: its tail call of null is pending through the handler and
the block, and traps when the frame is left (`return_call_ref-frame-null`). -/
theorem nuller_steps (f : Frame) (c : Admin) (hc : c.IsCallRef) :
    Steps P host ⟨tStoreV, f, vals [] ++ [.ref (.func 3), c]⟩ ⟨tStoreV, f, [.trap]⟩ :=
  ((closedCallXP_sound (P := P) (host := host) [tTag] tStoreV 3 [] _ nuller_answerV
    tStoreV_tagsOk).2 f _ [] [.num (.int .i32)] c tStoreV_storeChk rfl tTy_funcType rfl
    hc).2.2.1 rfl

end Core

end Silmaril.Proofs.Wasm.Interp.ExampleTailEH
