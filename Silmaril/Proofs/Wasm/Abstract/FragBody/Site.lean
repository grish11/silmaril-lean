module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Assembly
public import Silmaril.Wasm.Abstract.SSAFragment.Defs
import Silmaril.Wasm.Execution.Core.Soundness.PresCall
import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
import Silmaril.Wasm.Binaryen.UniformWf
import Silmaril.Wasm.SSA.Native.Thms
import Silmaril.Wasm.SSA.Pipeline.Thms

/-!
# Validated fragment sites are typed

`funcTyped_of_site`: the function of a validated fragment call site
(`IsFragmentSite`) is `funcTyped`. The store's typing (`StoreOk`) gives the
function instance's `Func_ok`: its body's lowering is valid in the body context
of its declared type, which validation bounds by the instance's type (`Sub`); with
integer parameters and results, the parameters are exactly the fragment's and the
results lie below its result type, so the body context fits the fragment
contexts (`Fit`) and `funcTyped_of_instrsOk` applies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.FragBody (funcTyped)

/-- The integer value types of a recognised list. -/
theorem mapM_ofValType_eq : ∀ {ts : List ValType} {us : List IntType},
    ts.mapM SSA.ofValType? = some us → ts = us.map fun t => .num (.int t)
  | [], us, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | t :: ts, us, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨u, hu, us', hus, rfl⟩ := h
    have ht : t = .num (.int u) := by
      rcases t with ⟨_ | _⟩ | _ | _ <;> simp only [SSA.ofValType?, reduceCtorEq,
        Option.some.injEq] at hu
      subst hu
      rfl
    rw [ht, mapM_ofValType_eq hus]
    rfl

/-- A recognised function's locals are its fragment locals. -/
theorem locals_of_frag {ft : FuncType} {bf : BFunc} {f : SSA.FragFunc}
    (h : SSA.ofBFunc? ft bf = some f) : bf.locals = f.locals.map fun t => .num (.int t) := by
  obtain ⟨params, results⟩ := ft
  rcases results with _ | ⟨t, _ | ⟨t₂, rest⟩⟩ <;>
    simp only [SSA.ofBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
  · obtain ⟨_, _, _, _, ls, hls, _, _, rfl⟩ := h
    exact mapM_ofValType_eq hls
  · obtain ⟨_, _, _, _, ls, hls, _, _, rfl⟩ := h
    exact mapM_ofValType_eq hls
  · simp at h

theorem liftVal_int (τs : List IntType) :
    (τs.map fun t => (ValType.num (.int t))).map liftVal = τs.map numInt := by
  simp [liftVal]

theorem liftVal_result (ρ : Option IntType) :
    (SSA.resultTypes ρ).map liftVal = ρ.toList.map numInt := by
  cases ρ <;> rfl

/-- The local types of a recognised function's declared locals. -/
theorem localOk_int {C : Context} :
    ∀ {τs : List IntType} {lts : List LocalType},
      List.Forall₂ (LocalOk C) (τs.map fun t => (ValType.num (.int t))) lts →
      lts.map LocalType.type = τs.map numInt
  | [], _, .nil => rfl
  | _ :: _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons, localOk_int hs]
    cases h <;> rfl

/-- **The validation link.** The function of a validated fragment call site is typed. -/
theorem funcTyped_of_site {H : Type} {x : Silmaril.Wasm.Abstract.CallSite H} {ft : FuncType}
    {bf : BFunc} {f : SSA.FragFunc} (hx : Silmaril.Wasm.Abstract.IsFragmentSite x ft bf f) :
    funcTyped f := by
  obtain ⟨fi, hfi, hcode, hft⟩ := hx.code
  have hs := hx.storeOk
  have hfit : TyOk {} fi.type := PC.StoreOk.func_tyOk hs hfi
  obtain ⟨hpar, hres⟩ := SSA.ofBFunc?_types hx.frag
  -- the instance's function type
  obtain ⟨ps, rs, he, hps, hrs⟩ : ∃ ps rs, Expand fi.type (.func ps rs) ∧
      ps.toList = f.params.map numInt ∧ rs.toList = f.result.toList.map numInt := by
    unfold DefType.funcType? at hft
    split at hft
    · rename_i ps rs hex
      simp only [Option.some.injEq, Prod.mk.injEq] at hft
      refine ⟨ps, rs, Expand.iff.mpr hex, ?_, ?_⟩
      · rw [hft.1, hpar, liftVal_int]
      · rw [hft.2, hres, liftVal_result]
    · cases hft
  cases hs.funcs fi (List.mem_of_getElem? hfi) with
  | host _ _ hcode' => rw [hcode] at hcode'; cases hcode'
  | @wasm C₁ code d' _ hm hcode' hfo hsd =>
    rw [hcode] at hcode'
    cases hcode'
    cases hfo with
    | @mk ps' rs' lts hd' he' hl hb =>
      have hΔ₁ := PC.ModuleInstOk.typesOk' hm
      obtain ⟨hloc0, -, -, -⟩ := ModuleInstOk.ctx_fields hm
      have hd'ok : TyOk {} d' := PC.TypesOk.get hΔ₁ hd'
      have hh := PC.heap_toEmpty hΔ₁ (.defDef hsd) (a := Ty.use (.dt d')) hd'ok (.use (.dt hfit))
      obtain ⟨hps', hrs'⟩ := PC.ds_func hd'ok hfit hh.1 he' he
      -- the module context and the body context are well formed
      have hC₁ : C₁.Wf := by
        have := FrameOk.ctxWf (f := { locals := [], module := fi.module }) hs
          ⟨hs.structsClosed, hs.arraysClosed⟩ ⟨C₁, [], hm, .nil, rfl⟩
        rwa [show ({ C₁ with locals := C₁.locals ++ [] } : Context) = C₁ by cases C₁; simp] at this
      have hD := BodyTransform.funcBody_wf hC₁ hd' he' hl
      -- parameters are exact, results lie below the fragment's
      have hpe : ps'.toList = f.params.map numInt := by
        rw [hps] at hps'; exact resultSub_nums hps' (nums_numInt _)
      have hrsub : ResultSub (C₁.funcBody ps'.toList rs'.toList lts).toTypeCtx rs'.toList
          (f.result.toList.map numInt) := hrs ▸ PC.resultSub_weaken hrs'
      have hlts : lts.map LocalType.type = f.locals.map numInt := by
        have hl' := hl
        rw [show (SSA.coreFunc bf).locals = bf.locals from rfl, locals_of_frag hx.frag] at hl'
        exact localOk_int hl'
      have hF : Fit (C₁.funcBody ps'.toList rs'.toList lts) (f.params ++ f.locals) f.result
          [f.result] := by
        refine ⟨fun y => ?_, .cons hrsub .nil, ⟨_, rfl, hrsub⟩⟩
        have hall : ((C₁.funcBody ps'.toList rs'.toList lts).locals.map LocalType.type) =
            (f.params ++ f.locals).map numInt := by
          simp only [Context.funcBody, List.map_append, List.map_map, hlts, hpe]
          rfl
        rw [← List.getElem?_map, hall, List.getElem?_map]
      exact funcTyped_of_instrsOk hD hF (SSA.ofBFunc?_body hx.frag) hx.native hrsub hb

end Silmaril.Proofs.Wasm.Abstract.FragBody
