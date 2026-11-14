module

public import Silmaril.Wasm.Abstract.Function.Thms
public import Silmaril.Wasm.Abstract.SSAFragment.Defs
public import Silmaril.Wasm.SSA.CoreCert.Thms

/-!
# λSSA fragment functions as abstract functions

A concrete correspondence through the actual Core 3.0 `Steps`, not a
denotation defined by fiat. Take a store with the Core code of a structured,
native λSSA fragment function `bf` at address `a`, satisfying the hypotheses of
`Silmaril.Wasm.SSA.behaviours_eq_run`. Then the abstract function
`wasmFun P closedHost a`, with its final store forgotten, has exactly the
fragment's run outcomes at every typed invocation, plus divergence when the
fragment has none (`wasmFun_ssaFragment`).

The proof composes two theorems: `image_wasmFun` (the projection agrees with
Core 3.0 `behaviours`) and `behaviours_eq_run` (Core 3.0 `behaviours` of such a
function are the fragment's runs, proved via the native interpreter's
adequacy). This is the first class of concrete Wasm functions whose abstract
function is determined by an independent source semantics, the λSSA fragment
`Run` relation.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA

variable {H : Type}

/-- The abstract function of a structured native λSSA fragment function is its
fragment run semantics (store forgotten), divergence included. -/
theorem wasmFun_ssaFragment {s : Store H} {a : Nat} {fi : FuncInst H} {ft : FuncType}
    {bf : BFunc} {f : FragFunc} (hs : StoreOk s) (hF : NativeFuncsOk s.funcs)
    (hS : Silmaril.Wasm.Interp.StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm (coreFunc bf))
    (hty : Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal))
    (hf : ofBFunc? ft bf = some f) (hn : f.native = true)
    (hst : BExpr.structuredList bf.body = true) {vs : List Val} (hok : InvokeOk s a vs)
    (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      (fun x => endToBehaviour x.2) '' wasmFun P closedHost a s vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} := by
  obtain ⟨args, h₁, h₂, h₃⟩ := behaviours_eq_run hs hF hS hfi hcode hty hf hn hst hok P
  exact ⟨args, h₁, h₂, (image_wasmFun P closedHost a s vs).trans h₃⟩

/-! ## The equivalence facade -/

/-- A call's behaviours are those of its abstract function, final store
forgotten. -/
theorem callSem_eq_image (P : Numerics.Profile) (x : CallSite H) (vs : List Val) :
    callSem P x vs = (fun y => endToBehaviour y.2) '' wasmFun P closedHost x.addr x.store vs :=
  (image_wasmFun P closedHost x.addr x.store vs).symm

/-- A call site of a fragment function has exactly its fragment runs as
behaviours. -/
theorem IsFragmentSite.callSem {x : CallSite H} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hx : IsFragmentSite x ft bf f) {vs : List Val} (hok : InvokeOk x.store x.addr vs)
    (P : Numerics.Profile) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      callSem P x vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} := by
  obtain ⟨fi, hfi, hcode, hty⟩ := hx.code
  exact behaviours_eq_run hx.storeOk hx.nativeOk hx.storeChk hfi hcode hty hx.frag hx.native
    hx.structured hok P

/-- **Equivalence from fragment runs.** Two fragment call sites whose fragment
run relations agree are call-equivalent: same Core 3.0 behaviours on every
typed invocation, every profile, divergence included. A CFG or region
interpretation proved equal to a fragment run relation gets this. -/
theorem callEquiv_of_run_iff {H' : Type} {x : CallSite H} {y : CallSite H'} {ft ft' : FuncType}
    {bf bf' : BFunc} {f f' : FragFunc} (hx : IsFragmentSite x ft bf f)
    (hy : IsFragmentSite y ft' bf' f')
    (hinv : ∀ vs, InvokeOk x.store x.addr vs → InvokeOk y.store y.addr vs)
    (hrun : ∀ args o, f.Run args o ↔ f'.Run args o) : CallEquiv x y := by
  intro P vs hok
  obtain ⟨args, hv, -, h₁⟩ := hx.callSem hok P
  obtain ⟨args', hv', -, h₂⟩ := hy.callSem (hinv vs hok) P
  obtain rfl := WVal.map_toVal_inj (hv.symm.trans hv')
  rw [h₁, h₂]
  ext b
  simp only [Set.mem_ofPred_eq, hrun]

/-- **Certified optimisations are call-equivalent.** If the run-time checked
λSSA optimiser accepts function `g` of module `m` with replacement `bf'`, the
allocated stores of `m` and of `m` with `g` replaced are call-equivalent at
`g`. -/
theorem optimize_callEquiv {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    ∃ s s' : Store Empty, allocStore? m = some s ∧ allocStore? (m.setFunc g bf') = some s' ∧
      CallEquiv (⟨s, g⟩ : CallSite Empty) (⟨s', g⟩ : CallSite Empty) := by
  obtain ⟨s, s', hs, hs', heq⟩ := coreChecked_spec h
  exact ⟨s, s', hs, hs', fun P vs hok => heq P vs hok⟩

/-- Call equivalence implies trap ≈ divergence equivalence of the behaviour sets. -/
theorem CallEquiv.trapDiv {H' : Type} {x : CallSite H} {y : CallSite H'} (h : CallEquiv x y)
    (P : Numerics.Profile) {vs : List Val} (hok : InvokeOk x.store x.addr vs) :
    Behaviours.Equiv Behaviour.TrapDiv (callSem P x vs) (callSem P y vs) := by
  rw [h P vs hok]
  exact ⟨fun b hb => ⟨b, hb, Behaviour.TrapDiv.refl b⟩, fun b hb => ⟨b, hb, Behaviour.TrapDiv.refl b⟩⟩

end Silmaril.Wasm.Abstract
