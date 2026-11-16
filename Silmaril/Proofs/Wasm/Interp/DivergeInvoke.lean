module

public import Silmaril.Proofs.Wasm.Interp.DivergeTyped
public import Silmaril.Proofs.Wasm.Interp.Div

/-!
# Native divergence of typed invocations (proofs)

For a typed invocation of a native, arity-checked store:

* `invokeRun_none_iff_funDiv`: the interpreter fails at every fuel exactly
  when the callee body diverges coinductively (`FunDiv`). The callee body is
  a good problem (`Good`), as in `divSim_det`, so `bad_le_evalDiv` applies.
* `diverges_iff_funDiv`: so, by native adequacy, Core 3.0 divergence is
  `FunDiv`, at every profile.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Execution.Core.Sim

variable {H : Type} {s : Store H} {a : Nat} {vs : List Val}

/-- A diverging body makes the interpreter fail at every fuel (any store). -/
theorem invokeRun_none_of_funDiv (h : FunDiv s a vs) (fuel : Nat) :
    Binaryen.invokeRun fuel s a vs = none := by
  obtain ⟨fi, fn, hfi, hcode, hd⟩ := h
  unfold Binaryen.invokeRun
  rw [hfi]
  rcases hty : Validation.DefType.funcType? fi.type with _ | ⟨ps, rs⟩
  · simp [hcode, hty]
  · rcases hr : Binaryen.run fuel s (Frame.forCall fi.module vs fn.locals) []
      (Binaryen.liftInstrs fn.body) with _ | r
    · simp [hcode, hty, hr]
    · exact absurd hd (eval_not_evalDiv (Binaryen.eval_of_run hr))

/-- The callee body of a typed invocation is a good problem. -/
theorem good_body (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) :
    ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ∃ ob, chk s.funcs fi.module (Frame.forCall fi.module vs fn.locals).locals.length rs.length
          [rs.length] (some 0) (Binaryen.liftInstrs fn.body) = some ob ∧
        Good s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body) := by
  obtain ⟨-, -, rts, -, -, hc⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  obtain ⟨fn, hcode, -⟩ := hF fi (List.mem_of_getElem? hfi)
  have hty := funcType_of_expand he
  have hlen : vs.length = ps'.toList.length := args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have enter := steps_invoke_enter (P := profile o₀) (host := Det.noHost) hfi hcode hty hlen
  rw [invoke_body_cfg] at enter
  have hct : ContextTyped
      (pcfg s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)) :=
    ContextTyped.label (ContextTyped.frame (ContextTyped.steps (ContextTyped.of_configOk hc) enter))
  obtain ⟨ob, hb, -⟩ := endsAt_eq (hS a fi fn _ _ hfi hcode hty)
  have hbc : chk s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs'.toList.length [rs'.toList.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [forCall_length _ _ hlen]
    exact hb
  exact ⟨fi, fn, _, _, hfi, hcode, hty, ob, hbc, _, _, _, hbc, hct, hF, hS⟩

/-- **The interpreter fails at every fuel exactly when the body diverges**, on
typed invocations of native, arity-checked stores. -/
theorem invokeRun_none_iff_funDiv (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    (∀ fuel, Binaryen.invokeRun fuel s a vs = none) ↔ FunDiv s a vs := by
  refine ⟨fun hnone => ?_, invokeRun_none_of_funDiv⟩
  obtain ⟨fi, fn, ps, rs, hfi, hcode, hty, ob, hbc, hg⟩ := good_body hs hF hS hok
  refine ⟨fi, fn, hfi, hcode, bad_le_evalDiv _ _ _ _ ⟨hg, ?_⟩⟩
  rintro ⟨⟨s', F', flb⟩, hev⟩
  obtain ⟨hokb, -⟩ := flowOk_of_eval hev hS hbc
  obtain ⟨fuel, hrun⟩ := Binaryen.run_of_eval hev
  exact invokeRun_some hfi hcode hty hrun (callee_flow hokb) (hnone fuel)

/-- **Core 3.0 divergence is native coinductive divergence**, every profile, on
typed invocations of native, arity-checked stores. -/
theorem diverges_iff_funDiv (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) (P : Profile) :
    Diverges P Binaryen.closedHost (invoke s a vs) ↔ FunDiv s a vs := by
  rw [← invokeRun_none_iff_funDiv hs hF hS hok]
  have he := behaviours_eq_nbeh_native (P := P) hs hF hS hok
  constructor
  · intro hd
    have hb : Behaviour.diverges ∈ behaviours P Binaryen.closedHost s a vs := .inr ⟨rfl, hd⟩
    rw [he] at hb
    rcases hb with ⟨_, _, fl, -, hfl⟩ | ⟨-, h⟩
    · rcases fl <;> simp [Binaryen.flowBeh] at hfl
    · exact h
  · intro h
    have hb : Behaviour.diverges ∈ behaviours P Binaryen.closedHost s a vs := by
      rw [he]
      exact .inr ⟨rfl, h⟩
    rcases hb with ⟨_, r, -, -, hr⟩ | ⟨-, hd⟩
    · cases r <;> simp [Result.toBehaviour] at hr
    · exact hd

end Silmaril.Wasm.Interp
