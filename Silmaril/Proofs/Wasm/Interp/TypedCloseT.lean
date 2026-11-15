module

public import Silmaril.Proofs.Wasm.Interp.TypedT
public import Silmaril.Proofs.Wasm.Interp.TypedCloseX
public import Silmaril.Proofs.Wasm.Interp.TailCloseX
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# The closure as a sound oracle for typed calls, tail calls included (proofs)

`TypedCloseX.oracleSoundX_typedClosed` for the tail checker `tExt`: the closure, restricted to
calls whose callee body is typed in context (`CX`), is a sound oracle for `tExt`
(`oracleSoundT_typedClosed`), every call form in callee bodies included, the three tail forms
among them. A tail callee is entered only after the caller's frame is left, so its typing does
not come by stepping the site: the site's typing gives the arguments the callee's parameter
types (`retRef_args`, from the `return_call_ref` typing as `PC.callRef_front` does for
`call_ref`), and a typed invocation types the callee's body (`entry_of_invokeOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

variable {P : Numerics.Profile}

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core.PC in
/-- **The arguments of a typed `return_call_ref` on a function reference** have the callee's
parameter types (as `PC.callRef_front` shows for `call_ref`). -/
theorem retRef_args {s : Store H} {C : Context} {it : InstrType} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hs : StoreOk s) (hC : C.Wf) (hΔ : PC.TypesOk C.toTypeCtx) (hcr : c.IsReturnCallRef)
    (hcd : ∀ d, c = .returnCallRefType d → TyOk {} d)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (h : AdminsOk s C (vals vs ++ [.ref (.func a), c]) it) :
    List.Forall₂ (ValOk s) vs ps.toList := by
  have hsT : PC.StoreTypesOk s := ⟨hs.structsClosed, hs.arraysClosed⟩
  have e0 : vals (vs ++ [.ref (.func a)]) ++ [c] = vals vs ++ [.ref (.func a), c] := by
    simp [vals, Val.toAdmin]
  have h' : AdminsOk s C (vals (vs ++ [.ref (.func a)]) ++ [c]) it := by rw [e0]; exact h
  obtain ⟨tvs', it₀, M, T, hc0, hvs', hsub, hM, hT, hMs, hP, -⟩ :=
    redex_rep hC (returnCallRef_inits hcr) h'
  obtain ⟨dc, psc, rsc, rs', t₃, t₄, hec, -, -, -, rfl, h1, h2⟩ := inv_returnCallRef hcr hc0
  have hdc : TyOk {} dc := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsReturnCallRef] at hcr
      exact PC.TypesOk.get hΔ (h1 _ rfl)
    | returnCallRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      exact hcd _ rfl
    | _ => simp [Admin.IsReturnCallRef] at hcr
  have hpc := Expand.func_ok hdc hec
  obtain ⟨tvs, trtl, rfl, hvs, htr⟩ := PC.forall₂_split_left hvs'
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub C.toTypeCtx ((it.params ++ tvs) ++ [trt])
      (((T ++ t₃) ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hC.types hM hsub hMs
    simpa using this
  obtain ⟨hX, htrs⟩ := PC.forall₂_append_eq_len hall rfl
  have htrc : Sub C.toTypeCtx trt (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub C.toTypeCtx rt (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : RefI (.ref false (Ty.defHeap fi.type)) := by
    simpa [RefI, HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fi.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok, hs0⟩
    · exact (ref_toEmpty hΔ hsubrt hI₀ hdcok).1
    · have hIrt := (ref_toEmpty typesOk_empty hs0 hI₀ hok).2
      exact Sub.trans TypeCtx.ok_empty hok hs0 (ref_toEmpty hΔ hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fi.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, -⟩ := ds_func hfit hdc hheap he hec
  have hlen : tvs.length = psc.toList.length := by
    have e1 := hvs.length_eq
    have e2 := hpsub.length_eq
    simp only [Ty.length] at hn
    omega
  obtain ⟨-, htv⟩ := PC.forall₂_append_eq_len hX hlen
  exact valsOk_transfer hs hsT typesOk_empty (valsOk_transfer hs hsT hΔ hvs htv hpc.1) hpsub
    (Expand.func_ok hfit he).1

include P in
/-- **A typed invocation types its callee's body.** -/
theorem entry_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (h : InvokeOk s a vs) : TypedEntry s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  obtain ⟨fi', ps', rs', hfi', -, hok⟩ := invoke_ok hs ⟨fi, ps, rs, hfi, he, hvs⟩
  rw [hfi] at hfi'; cases hfi'
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?
    rw [Validation.Expand.iff.mp he]
  have hct : Sim.ContextTyped ⟨s, {}, vals vs.reverse.reverse ++
      [.ref (.func a), .callRefType fi.type] ++ []⟩ := by
    simpa [invoke, hfi] using Sim.ContextTyped.of_configOk hok
  have hlen : ps.toList.length = vs.length := hvs.length_eq.symm
  have := entry_of_ref_site (P := P) hct trivial hfi hty (by simp [hlen])
  rwa [hlen, List.take_of_length_le (by simp), List.reverse_reverse] at this

include P in
/-- **A typed `return_call_ref` site on a function reference types its callee's body**, which
runs only after the caller's frame is left: the arguments have the callee's parameter types. -/
theorem entry_of_retRef_site {s : Store H} {f : Frame} {stk : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.ref (.func a), c] ++ rest⟩)
    (hcr : c.IsReturnCallRef) (hcd : ∀ d, c = .returnCallRefType d → Validation.TyOk {} d)
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hm : TyTypes f.module) (hp : ps.length ≤ stk.length) :
    TypedEntry s a (stk.take ps.length).reverse := by
  have ht' : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.ref (.func a), c]⟩ :=
    Sim.ContextTyped.suffix ht
  obtain ⟨C, ts, xs, hs, hC, htypes, hcode⟩ := ht'.fragment_types
  have e : vals stk.reverse ++ [.ref (.func a), c] = vals (stk.drop ps.length).reverse ++
      (vals (stk.take ps.length).reverse ++ [.ref (.func a), c]) := by
    rw [rev_take_drop stk ps.length]; simp
  obtain ⟨mid, xs₁, _, -, h₂, _⟩ := AdminsOk.split hcode hC (vals (stk.drop ps.length).reverse)
    (vals (stk.take ps.length).reverse ++ [.ref (.func a), c]) e (by simp)
  obtain ⟨ps', rs', hex, hpl, -⟩ := expand_of_funcType hty
  have hpp : ps.length = ps'.length := by rw [← hpl]
  have hn : (stk.take ps.length).reverse.length = ps'.length := by
    rw [← hpp]; simp only [List.length_reverse, List.length_take]; omega
  have hΔ : PC.TypesOk (C.initLocals xs₁).toTypeCtx := fun d hd => by
    rw [Validation.Context.initLocals_toTypeCtx] at hd
    have : d ∈ f.module.types := by rw [← htypes]; simpa [Validation.Context.toTypeCtx] using hd
    obtain ⟨n, hn⟩ := List.getElem?_of_mem this
    exact hm n d hn
  exact entry_of_invokeOk (P := P) hs ⟨fi, ps', rs', hfi, hex,
    retRef_args hs (hC.initLocals xs₁) hΔ hcr hcd hfi hex hn h₂⟩

include P in
/-- **A typed, resolved tail call site types its callee's body** (`return_call`,
`return_call_indirect`, `return_call_ref`). -/
theorem entry_of_tail_site {i : Instr} {s : Store H} {f : Frame} {stk : List Val}
    {rest : List Admin} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {labels : List Nat} {ret : Nat} {o : Option Nat}
    (hsite : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (hres : TailRes s f i stk (some (fa, stk.drop (tailPop i))))
    (hfi : s.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : ∀ y, tailAnn i = some y → typeArity f.module y = some (ps.length, rs.length))
    (hTF : TyFuncs s) (hTM : TyTypes f.module)
    (hf : flatChkE tExt s.funcs f.module f.locals.length ret labels stk.length i = some o) :
    TypedEntry s fa ((stk.drop (tailPop i)).take ps.length).reverse := by
  obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hf
  obtain ⟨c, hcr, hcd, hpre⟩ := tailRes_steps (P := P) (host := noHostX) hres
  have e : vals stk.reverse ++ .plain i :: rest = vals (stk.drop (tailPop i)).reverse ++
      (vals (stk.take (tailPop i)).reverse ++ [.plain i]) ++ rest := by
    rw [rev_take_drop stk (tailPop i)]; simp
  rw [e] at hsite
  have ht := Sim.ContextTyped.steps hsite
    (Steps.ctx (P := P) (host := noHostX) (stk.drop (tailPop i)).reverse rest hpre)
  refine entry_of_retRef_site (P := P) ht hcr (fun d hd => ?_) hfi hty hTM
    (by simp only [List.length_drop]; omega)
  obtain ⟨fi', hfi', rfl⟩ := hcd d hd
  exact hTF _ _ hfi'

include P in
/-- A typed `call x` site types its callee's body. -/
theorem entry_of_call_siteT {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} {a : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType} {labels : List Nat}
    {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.call x) :: rest⟩)
    (hfi : s.func? f x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hc : flatChkE tExt s.funcs f.module f.locals.length ret labels stk.length (.call x) = some o) :
    TypedEntry s a (stk.take ps.length).reverse := by
  obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hc)
  rw [callArity_eq hfi hty, Option.some.injEq, Prod.mk.injEq] at hpq
  obtain ⟨rfl, rfl⟩ := hpq
  have hst := Step.ctx (P := P) (host := noHostX) stk.reverse rest
    (Step.call (s := s) (f := f) (module_of_func? hfi) (funcs_of_func? hfi))
  have e : vals stk.reverse ++ .plain (.call x) :: rest = vals stk.reverse ++ [.plain (.call x)] ++ rest := by
    simp
  rw [e] at ht
  exact entry_of_ref_site (P := P) (Sim.ContextTyped.step ht hst) trivial (funcs_of_func? hfi) hty hp

include P in
/-- A typed `call_indirect` site, resolved, types its callee's body. -/
theorem entry_of_ind_siteT {s : Store H} {f : Frame} {stk : List Val} {x : TableIdx} {y : TypeIdx}
    {ad : AddrType} {i : BitVec ad.intType.width} {fa : Nat} {rest : List Admin} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {labels : List Nat} {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals (.num ⟨.int ad.intType, i⟩ :: stk).reverse ++
      .plain (.callIndirect x y) :: rest⟩)
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s f x y ad i (some fa)) (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length))
    (hc : flatChkE tExt s.funcs f.module f.locals.length ret labels
      (.num ⟨.int ad.intType, i⟩ :: stk).length (.callIndirect x y) = some o) :
    TypedEntry s fa (stk.take ps.length).reverse := by
  obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hc
  simp only [List.length_cons] at hp
  have hst := Steps.ctx (P := P) (host := noHostX) stk.reverse rest
    (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
  have e : vals (.num ⟨.int ad.intType, i⟩ :: stk).reverse ++ .plain (.callIndirect x y) :: rest =
      vals stk.reverse ++ [aconst ad i, .plain (.callIndirect x y)] ++
        rest := by
    rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
  rw [e] at ht
  exact entry_of_ref_site (P := P) (Sim.ContextTyped.steps ht hst) trivial hfi hty (by omega)

include P in
/-- A typed `call_ref` site types its callee's body. -/
theorem entry_of_callRef_siteT {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx} {fa : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType} {labels : List Nat}
    {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest⟩)
    (hfi : s.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length))
    (hc : flatChkE tExt s.funcs f.module f.locals.length ret labels
      (.ref (.func fa) :: stk).length (.callRef y) = some o) :
    TypedEntry s fa (stk.take ps.length).reverse := by
  obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hc
  simp only [List.length_cons] at hp
  have e : vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest =
      vals stk.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ rest := by simp [vals]; rfl
  rw [e] at ht
  exact entry_of_ref_site (P := P) ht trivial hfi hty (by omega)

section
variable {C : Abstract.CallRel H} (hC : OracleSoundT P noHostX (CX C)) (hCk : KeepsTy C)
include hC hCk

/-- **Typed runs make typed calls.** A typed run under `C` (the hypotheses of
`evalOXT_of_typed`) is an `EvalOXT` run under `C` restricted to calls whose callee body is
typed in context (`CX C`). -/
theorem evalOXT_restrictT {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX C s f stk es r) :
    TypedT s f stk es → EvalOXT (CX C) s f stk es r := by
  have hCkX : KeepsTy (CX C) := fun s a us out h hs => hCk s a us out h.2 hs
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih => exact fun ht => .argsAbort (ih (args_typedT ht)) hfl
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hc' : CX C _ _ _ _ := ⟨entry_of_call_siteT (P := P) hsite hfi hty hf, hcall⟩
    exact .callOk dA hfi hty hc' hvs
      (ihk (cont_typedT (P := P) hC hCkX (.callOk dA hfi hty hc' hvs .nil) ht))
  | callTrap _ hfi hty hcall iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    exact .callTrap dA hfi hty ⟨entry_of_call_siteT (P := P) hsite hfi hty hf, hcall⟩
  | callThrow _ hfi hty hcall iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    exact .callThrow dA hfi hty ⟨entry_of_call_siteT (P := P) hsite hfi hty hf, hcall⟩
  | opOk hi _ hflat _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    exact .opOk hi dA hflat (ihk (cont_typedT (P := P) hC hCkX (.opOk hi dA hflat .nil) ht))
  | opStop hi _ hflat hfl iha => exact fun ht => .opStop hi (iha (args_typedT ht)) hflat hfl
  | blockOk har _ hvs _ ihb ihk =>
    intro ht
    have dB := ihb (block_body_typedT (P := P) har ht)
    exact .blockOk har dB hvs (ihk (cont_typedT (P := P) hC hCkX (.blockOk har dB hvs .nil) ht))
  | blockBrk har _ ihb => exact fun ht => .blockBrk har (ihb (block_body_typedT (P := P) har ht))
  | blockEsc har _ hfl ihb =>
    exact fun ht => .blockEsc har (ihb (block_body_typedT (P := P) har ht)) hfl
  | loopOk har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedT (P := P) har ht)
    exact .loopOk har dB (ihk (cont_typedT (P := P) hC hCkX (.loopOk har dB .nil) ht))
  | loopBack har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedT (P := P) har ht)
    exact .loopBack har dB (ihk (loop_back_typedT (P := P) hC hCkX har dB ht))
  | loopBrk har _ ihb => exact fun ht => .loopBrk har (ihb (loop_body_typedT (P := P) har ht))
  | loopEsc har _ hfl ihb =>
    exact fun ht => .loopEsc har (ihb (loop_body_typedT (P := P) har ht)) hfl
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    intro ht
    have dC := ihc (cond_typedT ht)
    have dA := iharm (arm_typedT (P := P) hC hCkX dC hb har ht)
    exact .ifOk dC hb har dA hvs (ihk (cont_typedT (P := P) hC hCkX (.ifOk dC hb har dA hvs .nil) ht))
  | ifBrk _ hb har _ ihc iharm =>
    intro ht
    have dC := ihc (cond_typedT ht)
    exact .ifBrk dC hb har (iharm (arm_typedT (P := P) hC hCkX dC hb har ht))
  | ifEsc _ hb har _ hfl ihc iharm =>
    intro ht
    have dC := ihc (cond_typedT ht)
    exact .ifEsc dC hb har (iharm (arm_typedT (P := P) hC hCkX dC hb har ht)) hfl
  | ifAbort _ hfl ihc => exact fun ht => .ifAbort (ihc (cond_typedT ht)) hfl
  | callIndOk _ hres hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
    have hc' : CX C _ _ _ _ := ⟨entry_of_ind_siteT (P := P) hsite hres hfi hty hy hf, hcall⟩
    exact .callIndOk dA hres hfi hty hy hc' hvs
      (ihk (cont_typedT (P := P) hC hCkX (.callIndOk dA hres hfi hty hy hc' hvs .nil) ht))
  | callIndRes _ hres iha => exact fun ht => .callIndRes (iha (args_typedT ht)) hres
  | callIndStop _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChkT hf)
    exact .callIndStop dA hres hfi hty hy
      ⟨entry_of_ind_siteT (P := P) hsite hres hfi hty hy hf, hcall⟩ hfl
  | callRefOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨rest, hsite, hTF, hTM, _, _, _, -, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    have hc' : CX C _ _ _ _ := ⟨entry_of_callRef_siteT (P := P) hsite hfi hty hy hf, hcall⟩
    exact .callRefOk dA hfi hty hy hc' hvs
      (ihk (cont_typedT (P := P) hC hCkX (.callRefOk dA hfi hty hy hc' hvs .nil) ht))
  | callRefNull _ iha => exact fun ht => .callRefNull (iha (args_typedT ht))
  | callRefStop _ hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨rest, hsite, hTF, hTM, _, _, _, -, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    exact .callRefStop dA hfi hty hy ⟨entry_of_callRef_siteT (P := P) hsite hfi hty hy hf, hcall⟩ hfl
  | tail _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedT ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedT (P := P) hC hCkX dA ht
    have hy := tailAnn_typed hres hsite hfi hty hTF hTM hf
    exact .tail dA hres hfi hty hy ⟨entry_of_tail_site (P := P) hsite hres hfi hty hy hTF hTM hf, hcall⟩ hfl
  | tailRes _ hres iha => exact fun ht => .tailRes (iha (args_typedT ht)) hres

end

/-- **The closure is a sound oracle for typed calls**, every call form in callee bodies
included: least-fixpoint induction, each callee body typed in context running under the
closure restricted to typed calls (`evalOXT_restrictT`). -/
theorem oracleSoundT_typedClosed : OracleSoundT P noHostX (CX (closedCallX : Abstract.CallRel H)) := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallX s a us out ∧ (TypedEntry s a us → SoundAnsT P noHostX s a us out)
  have hQ : (closedCallX : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us ⟨s₂, fl⟩ ⟨fi, fn, ps₀, rs₀, f₂, hfi, hcode, hty₀, d⟩
    refine ⟨?_, fun hE => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps₀, rs₀, f₂, hfi, hcode, hty₀, d.mono fun _ _ _ _ h => h.1⟩
    · intro f' fi' ps rs c hS hfi' hty hn hcr
      rw [hfi] at hfi'; cases hfi'
      have hCX : OracleSoundT P noHostX (CX Q) :=
        fun s s₂ f a fi ps rs us fl c hS hfi hty hn hcr hcall =>
          hcall.2.2 hcall.1 f fi ps rs c hS hfi hty hn hcr
      have hCk : KeepsTy Q := fun _ _ _ _ h hs a fi hfi => hs a fi (closedCallX_funcs h.1 ▸ hfi)
      -- the body is a typed problem
      have hct := hE fi fn hfi hcode
      obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types hct
      have hend := hS a fi fn ps rs hfi hcode hty
      obtain ⟨ob, hb, -⟩ := endsAt_eq hend
      have hlen : (Frame.forCall fi.module us fn.locals).locals.length =
          ps.length + fn.locals.length := forCall_length _ _ hn
      have htyped : TypedT s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) := by
        refine ⟨[], [rs.length], rs.length, ob, hS, by rw [hlen]; exact hb, ?_,
          fun a fi hfi => PC.StoreOk.func_tyOk hsok hfi, tyTypes_of_storeOkX hsok hfi hcode⟩
        simpa [vals, Binaryen.lowerList_liftInstrs] using hct
      exact soundAnsT_of_bodyT (P := P) hCX hfi hcode (evalOXT_restrictT (P := P) hCX hCk d htyped)
        f' fi ps rs c hS hfi hty hn hcr
  intro s s₂ f a fi ps rs us fl c hS hfi hty hn hcr ⟨hE, hcl⟩
  exact (hQ _ _ _ _ hcl).2 hE f fi ps rs c hS hfi hty hn hcr

/-- **Typed closed extended runs are Core 3.0 runs**, every call form included (indirect,
reference and the three tail forms), in the running code and in every callee, under the
tail-aware postcondition. -/
theorem evalOX_closed_typed_goodT {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOX closedCallX s f stk es r) (ht : TypedT s f stk es) :
    ArityGoodE tExt s f stk es r ∧ CoreGoodT tExt P noHostX s f stk es r :=
  evalOXT_goodT oracleSoundT_typedClosed
    (evalOXT_restrictT (P := P) oracleSoundT_typedClosed keepsTy_closedCallX h ht)

end Silmaril.Wasm.Interp
