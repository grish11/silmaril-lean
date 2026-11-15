module

public import Silmaril.Proofs.Wasm.Interp.TypedX
public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall

/-!
# The closure as a sound oracle for typed calls, `call_ref` included (proofs)

`OracleCloseX.oracleSoundX_closedX` closes the oracle on stores whose function bodies have no
`call_ref`. This module drops that restriction for *typed* calls: a call whose callee body is
typed in context (`TypedEntry`). Every call of a typed run is one: its site is typed, steps by
Core 3.0 into the callee's frame, and preservation types the body (`entry_of_ref_site`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

/-- The callee body of a call is typed in context. -/
def TypedEntry (s : Store H) (a : Nat) (us : List Val) : Prop :=
  ∀ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    Sim.ContextTyped ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩

/-- **A typed call site types its callee's body.** At `[ref.func a, c]` (any `call_ref` form)
on the arguments, the callee's frame is entered by `call_ref-func`; preservation types it. -/
theorem entry_of_ref_site {P : Numerics.Profile} {s : Store H} {f : Frame} {stk : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.ref (.func a), c] ++ rest⟩)
    (hc : c.IsCallRef) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk.length) :
    TypedEntry s a (stk.take ps.length).reverse := by
  intro fi' fn hfi' hcode
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨ps', rs', he, hpl, -⟩ := expand_of_funcType hty
  have hpp : ps.length = ps'.length := by rw [← hpl]
  have hn : (stk.take ps.length).reverse.length = ps'.length := by
    rw [← hpp]; simp only [List.length_reverse, List.length_take]; omega
  have e : vals stk.reverse ++ [.ref (.func a), c] ++ rest =
      vals (stk.drop ps.length).reverse ++
        (vals (stk.take ps.length).reverse ++ [.ref (.func a), c]) ++ rest := by
    rw [rev_take_drop stk ps.length]; simp
  rw [e] at ht
  have hst := Step.ctx (P := P) (host := noHostX) (stk.drop ps.length).reverse rest
    (Step.callRefFunc (s := s) (f := f) hc hfi he hn hcode)
  exact Sim.ContextTyped.label (vs := []) (rest := [])
    (by simpa [vals] using Sim.ContextTyped.frame (Sim.ContextTyped.step ht hst))

variable {P : Numerics.Profile}

include P in
/-- A typed `call x` site types its callee's body. -/
theorem entry_of_call_site {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} {a : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType} {labels : List Nat}
    {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain (.call x) :: rest⟩)
    (hfi : s.func? f x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hc : flatChkE irExt s.funcs f.module f.locals.length ret labels stk.length (.call x) = some o) :
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
theorem entry_of_ind_site {s : Store H} {f : Frame} {stk : List Val} {x : TableIdx} {y : TypeIdx}
    {ad : AddrType} {i : BitVec ad.intType.width} {fa : Nat} {rest : List Admin} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {labels : List Nat} {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals (.num ⟨.int ad.intType, i⟩ :: stk).reverse ++
      .plain (.callIndirect x y) :: rest⟩)
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s f x y ad i (some fa)) (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length))
    (hc : flatChkE irExt s.funcs f.module f.locals.length ret labels
      (.num ⟨.int ad.intType, i⟩ :: stk).length (.callIndirect x y) = some o) :
    TypedEntry s fa (stk.take ps.length).reverse := by
  obtain ⟨hp, -⟩ := flatChk_ir (.inl ⟨_, rfl⟩) hy hc
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
theorem entry_of_callRef_site {s : Store H} {f : Frame} {stk : List Val} {y : TypeIdx} {fa : Nat}
    {rest : List Admin} {fi : FuncInst H} {ps rs : List Validation.CValType} {labels : List Nat}
    {ret : Nat} {o : Option Nat}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest⟩)
    (hfi : s.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length))
    (hc : flatChkE irExt s.funcs f.module f.locals.length ret labels
      (.ref (.func fa) :: stk).length (.callRef y) = some o) :
    TypedEntry s fa (stk.take ps.length).reverse := by
  obtain ⟨hp, -⟩ := flatChk_ir (.inr rfl) hy hc
  simp only [List.length_cons] at hp
  have e : vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest =
      vals stk.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ rest := by simp [vals]; rfl
  rw [e] at ht
  exact entry_of_ref_site (P := P) ht trivial hfi hty (by omega)

/-- An oracle restricted to calls whose callee body is typed in context. -/
def CX (C : Abstract.CallRel H) : Abstract.CallRel H := fun s a us out => TypedEntry s a us ∧ C s a us out

section
variable {C : Abstract.CallRel H} (hC : OracleSoundX P noHostX (CX C)) (hCk : KeepsTy C)
include hC hCk

/-- **Typed runs make typed calls.** A typed run under `C` (the hypotheses of
`evalOXT_of_typed`) is an `EvalOXT` run under `C` restricted to calls whose callee body is
typed in context (`CX C`). -/
theorem evalOXT_restrict {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX C s f stk es r) :
    TypedX s f stk es → EvalOXT (CX C) s f stk es r := by
  have hCkX : KeepsTy (CX C) := fun s a us out h hs => hCk s a us out h.2 hs
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih => exact fun ht => .argsAbort (ih (args_typedX ht)) hfl
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    have hc' : CX C _ _ _ _ := ⟨entry_of_call_site (P := P) hsite hfi hty hf, hcall⟩
    exact .callOk dA hfi hty hc' hvs
      (ihk (cont_typedX (P := P) hC hCkX (.callOk dA hfi hty hc' hvs .nil) ht))
  | callTrap _ hfi hty hcall iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    exact .callTrap dA hfi hty ⟨entry_of_call_site (P := P) hsite hfi hty hf, hcall⟩
  | callThrow _ hfi hty hcall iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, hsite, -, -, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    exact .callThrow dA hfi hty ⟨entry_of_call_site (P := P) hsite hfi hty hf, hcall⟩
  | opOk hi _ hflat _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    exact .opOk hi dA hflat (ihk (cont_typedX (P := P) hC hCkX (.opOk hi dA hflat .nil) ht))
  | opStop hi _ hflat hfl iha => exact fun ht => .opStop hi (iha (args_typedX ht)) hflat hfl
  | blockOk har _ hvs _ ihb ihk =>
    intro ht
    have dB := ihb (block_body_typedX (P := P) har ht)
    exact .blockOk har dB hvs (ihk (cont_typedX (P := P) hC hCkX (.blockOk har dB hvs .nil) ht))
  | blockBrk har _ ihb => exact fun ht => .blockBrk har (ihb (block_body_typedX (P := P) har ht))
  | blockEsc har _ hfl ihb =>
    exact fun ht => .blockEsc har (ihb (block_body_typedX (P := P) har ht)) hfl
  | loopOk har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedX (P := P) har ht)
    exact .loopOk har dB (ihk (cont_typedX (P := P) hC hCkX (.loopOk har dB .nil) ht))
  | loopBack har _ _ ihb ihk =>
    intro ht
    have dB := ihb (loop_body_typedX (P := P) har ht)
    exact .loopBack har dB (ihk (loop_back_typedX (P := P) hC hCkX har dB ht))
  | loopBrk har _ ihb => exact fun ht => .loopBrk har (ihb (loop_body_typedX (P := P) har ht))
  | loopEsc har _ hfl ihb =>
    exact fun ht => .loopEsc har (ihb (loop_body_typedX (P := P) har ht)) hfl
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    intro ht
    have dC := ihc (cond_typedX ht)
    have dA := iharm (arm_typedX (P := P) hC hCkX dC hb har ht)
    exact .ifOk dC hb har dA hvs (ihk (cont_typedX (P := P) hC hCkX (.ifOk dC hb har dA hvs .nil) ht))
  | ifBrk _ hb har _ ihc iharm =>
    intro ht
    have dC := ihc (cond_typedX ht)
    exact .ifBrk dC hb har (iharm (arm_typedX (P := P) hC hCkX dC hb har ht))
  | ifEsc _ hb har _ hfl ihc iharm =>
    intro ht
    have dC := ihc (cond_typedX ht)
    exact .ifEsc dC hb har (iharm (arm_typedX (P := P) hC hCkX dC hb har ht)) hfl
  | ifAbort _ hfl ihc => exact fun ht => .ifAbort (ihc (cond_typedX ht)) hfl
  | callIndOk _ hres hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChk hf)
    have hc' : CX C _ _ _ _ := ⟨entry_of_ind_site (P := P) hsite hres hfi hty hy hf, hcall⟩
    exact .callIndOk dA hres hfi hty hy hc' hvs
      (ihk (cont_typedX (P := P) hC hCkX (.callIndOk dA hres hfi hty hy hc' hvs .nil) ht))
  | callIndRes _ hres iha => exact fun ht => .callIndRes (iha (args_typedX ht)) hres
  | callIndStop _ hres hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, hsite, hTF, hTM, _, _, _, _, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    have hy := typeArity_of_indRes hres hfi hty hTF hTM (types_some_of_flatChk hf)
    exact .callIndStop dA hres hfi hty hy
      ⟨entry_of_ind_site (P := P) hsite hres hfi hty hy hf, hcall⟩ hfl
  | callRefOk _ hfi hty hcall hvs _ iha ihk =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨rest, hsite, hTF, hTM, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    have hc' : CX C _ _ _ _ := ⟨entry_of_callRef_site (P := P) hsite hfi hty hy hf, hcall⟩
    exact .callRefOk dA hfi hty hy hc' hvs
      (ihk (cont_typedX (P := P) hC hCkX (.callRefOk dA hfi hty hy hc' hvs .nil) ht))
  | callRefNull _ iha => exact fun ht => .callRefNull (iha (args_typedX ht))
  | callRefStop _ hfi hty hcall hfl iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨rest, hsite, hTF, hTM, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    have hy := typeArity_of_callRef_site hsite hTM hfi hty (hTF _ _ hfi)
    exact .callRefStop dA hfi hty hy ⟨entry_of_callRef_site (P := P) hsite hfi hty hy hf, hcall⟩ hfl
  | tail _ hres _ _ _ _ iha =>
    intro ht
    have dA := iha (args_typedX ht)
    obtain ⟨_, -, -, -, _, _, _, -, hf⟩ := site_typedX (P := P) hC hCkX dA ht
    rw [flatChk_tail hres] at hf
    cases hf
  | tailRes _ hres iha => exact fun ht => .tailRes (iha (args_typedX ht)) hres

end

/-- Valid instance types of a typed store's Wasm functions. -/
theorem tyTypes_of_storeOkX {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    {fn : Func} (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm fn) : TyTypes fi.module := by
  cases hs.funcs fi (List.mem_of_getElem? hfi) with
  | wasm _ hm _ _ _ =>
    obtain ⟨-, -, -, ht⟩ := ModuleInstOk.ctx_fields hm
    intro y d hd
    exact PC.TypesOk.get (PC.ModuleInstOk.typesOk' hm) (x := y)
      (by simpa [Validation.Context.toTypeCtx, ht] using hd)
  | host _ _ hc' => rw [hc] at hc'; cases hc'

theorem keepsTy_closedCallX : KeepsTy (closedCallX : Abstract.CallRel H) :=
  fun _ _ _ _ h hs a fi hfi => hs a fi (closedCallX_funcs h ▸ hfi)

/-- **The closure is a sound oracle for typed calls**, every call form in callee bodies
included: least-fixpoint induction, each callee body typed in context running under the
closure restricted to typed calls (`evalOXT_restrict`). -/
theorem oracleSoundX_typedClosed : OracleSoundX P noHostX (CX (closedCallX : Abstract.CallRel H)) := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallX s a us out ∧ (TypedEntry s a us → SoundAns P noHostX s a us out)
  have hQ : (closedCallX : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us ⟨s₂, fl⟩ ⟨fi, fn, ps₀, rs₀, f₂, hfi, hcode, hty₀, d⟩
    refine ⟨?_, fun hE => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps₀, rs₀, f₂, hfi, hcode, hty₀, d.mono fun _ _ _ _ h => h.1⟩
    · intro f' fi' ps rs c hS hfi' hty hn hcr
      rw [hfi] at hfi'; cases hfi'
      have hCX : OracleSoundX P noHostX (CX Q) :=
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
      have htyped : TypedX s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) := by
        refine ⟨[], [rs.length], rs.length, ob, hS, by rw [hlen]; exact hb, ?_,
          fun a fi hfi => PC.StoreOk.func_tyOk hsok hfi, tyTypes_of_storeOkX hsok hfi hcode⟩
        simpa [vals, Binaryen.lowerList_liftInstrs] using hct
      exact soundAns_of_bodyT (P := P) hCX hfi hcode (evalOXT_restrict (P := P) hCX hCk d htyped)
        f' fi ps rs c hS hfi hty hn hcr
  intro s s₂ f a fi ps rs us fl c hS hfi hty hn hcr ⟨hE, hcl⟩
  exact (hQ _ _ _ _ hcl).2 hE f fi ps rs c hS hfi hty hn hcr

/-- **Typed closed extended runs are Core 3.0 runs**, `call_indirect` and `call_ref` included,
in the running code and in every callee. -/
theorem evalOX_closed_typed_good {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOX closedCallX s f stk es r) (ht : TypedX s f stk es) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P noHostX s f stk es r :=
  evalOXT_goodE oracleSoundX_typedClosed
    (evalOXT_restrict (P := P) oracleSoundX_typedClosed keepsTy_closedCallX h ht)

end Silmaril.Wasm.Interp
