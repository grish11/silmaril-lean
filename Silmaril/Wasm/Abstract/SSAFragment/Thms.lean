module

public import Silmaril.Wasm.Abstract.Function.Thms
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

end Silmaril.Wasm.Abstract
