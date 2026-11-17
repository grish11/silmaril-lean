module

public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Wasm.Cfg.MachineLClose.Thms
public import Silmaril.Wasm.Abstract.TypedCatValid.Thms

@[expose] public section

/-!
# Typed-invocation hypotheses from validation (H3, proofs)

`funcType_of_invokeOk`: the premises of `$invoke` (`InvokeOk`) give the function's type and the
exact parameter count. `storeCtx_good_of_storeOk`: a valid store (`StoreOk`) with the checker's
acceptance of its functions gives the context hypothesis `Ctx.Good` at its own tags.
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgValid

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.Abstract.TypedCatValid (storeCtx)

variable {H : Type}

theorem funcType_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hok : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi) :
    ∃ ps rs : List Validation.CValType,
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ vs.length = ps.length := by
  obtain ⟨fi', ps', rs', hfi', he', hvs⟩ := hok
  rw [hfi] at hfi'; cases hfi'
  refine ⟨ps'.toList, rs'.toList, ?_, hvs.length_eq⟩
  unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he']

theorem storeCtx_good_of_storeOk {s : Store H} (hs : StoreOk s)
    (hchk : StoreChkE (ehExt s.tags) s.funcs) : (storeCtx s.tags s hchk).Good s :=
  (Abstract.TypedCatValid.storeCtx_good hchk).2 (Abstract.TypedCatValid.tagsOk_of_storeOk hs)

end Silmaril.Wasm.Cfg.Proofs.CfgValid
