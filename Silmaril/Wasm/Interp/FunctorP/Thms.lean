module

public import Silmaril.Wasm.Abstract.FunctorP.Thms
public import Silmaril.Wasm.Interp.PProgress.Thms
import Silmaril.Proofs.Wasm.Interp.FunctorP

/-!
# Soundness of the denotational equational theory for closed Core 3.0 observations (F7)

Two Wasm functions `a` and `b` of one store whose exposed frames agree (`ExposeP.frameXP a vs`
and `frameXP b vs` are the same interaction tree at the invocation's store; by
`FunctorP.frameXP_run_eq` this holds when they share module instance and locals and their bodies
are operationally equivalent, `FunctorP.OpEquivP`, equivalently have equal denotations up to trap
payloads, `FunctorP.opEquivP_iff`) have the same closed Core 3.0 observations
(`invoke_obs_of_frame`, `invoke_obs_of_opEquivP`):

* the same divergence;
* the same normal forms other than a trap: the same values (with the final store) and the same
  uncaught exception (`throwing t`, with the final store);
* a trap exactly when the other traps.

**Hypotheses** (those of `PProgress.invoke_closedXP_adequacy`, for both invocations): a typed
store (`StoreOk`), typed invocations (`InvokeOk`), every function passing the exception checker
(`StoreChkE (ehExt tags)`), Wasm functions with function types (`WasmFuncsT`), the tag invariants
(`TagsOk tags`), a deterministic profile `profile o`, the closed host `noHostX`; and the same
result count (`rs.length = rs'.length`), which Core reads off the callee's type.

**Not claimed.** The store a trap leaves: the denotation's trap is the trap effect of `BodyM`,
which forgets the store, so equal denotations may trap in different stores (one function may write
memory before trapping). This is soundness of the equational theory for the **closed,
deterministic, no-host** setting only: the oracle is the closure `closedCallXP`. Host calls,
observations of host interaction and infinite traces (`HostSquare`, `HostClosingInf`) are out of
scope here (another owner).
-/

public section

namespace Silmaril.Wasm.Interp.FunctorP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall Silmaril.Wasm.Abstract.ExposeP

variable {H : Type}

/-- **Equal frames, equal closed Core 3.0 observations.** -/
theorem invoke_obs_of_frame {tags : List TagInst} {o : GrowOracle} {s : Store H} {a b : Nat}
    {vs : List Val} {fi fi' : FuncInst H} {ps rs ps' rs' : List Validation.CValType}
    (hs : StoreOk s) (hoka : InvokeOk s a vs) (hokb : InvokeOk s b vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hfa : s.funcs[a]? = some fi) (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hrs : rs.length = rs'.length)
    (hfr : ((frameXP a vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run =
      ((frameXP b vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run) :
    (Diverges (profile o) noHostX (invoke s a vs) ↔ Diverges (profile o) noHostX (invoke s b vs)) ∧
    (∀ c' : Config H, c'.code ≠ [.trap] →
      ((Steps (profile o) noHostX (invoke s a vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x) ↔
        (Steps (profile o) noHostX (invoke s b vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x))) ∧
    ((∃ s₂, Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, [.trap]⟩) ↔
      ∃ s₂, Steps (profile o) noHostX (invoke s b vs) ⟨s₂, {}, [.trap]⟩) :=
  Silmaril.Proofs.Wasm.Interp.FunctorP.invoke_obs_of_frame hs hoka hokb hS hW hts hfa htya hfb
    htyb hrs hfr

/-- **Operationally equivalent bodies, equal closed Core 3.0 observations**: two Wasm functions
with the same module instance, locals and result count whose bodies are operationally
equivalent (`FunctorP.OpEquivP`, i.e. equal denotations up to trap payloads). -/
theorem invoke_obs_of_opEquivP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a b : Nat}
    {vs : List Val} {fi fi' : FuncInst H} {fn fn' : Func} {ps rs ps' rs' : List Validation.CValType}
    (hs : StoreOk s) (hoka : InvokeOk s a vs) (hokb : InvokeOk s b vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hfa : s.funcs[a]? = some fi) (hca : fi.code = .wasm fn)
    (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (hcb : fi'.code = .wasm fn')
    (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hrs : rs.length = rs'.length) (hmod : fi.module = fi'.module) (hloc : fn.locals = fn'.locals)
    (hbody : Abstract.FunctorP.OpEquivP H (liftInstrs fn.body) (liftInstrs fn'.body)) :
    (Diverges (profile o) noHostX (invoke s a vs) ↔ Diverges (profile o) noHostX (invoke s b vs)) ∧
    (∀ c' : Config H, c'.code ≠ [.trap] →
      ((Steps (profile o) noHostX (invoke s a vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x) ↔
        (Steps (profile o) noHostX (invoke s b vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x))) ∧
    ((∃ s₂, Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, [.trap]⟩) ↔
      ∃ s₂, Steps (profile o) noHostX (invoke s b vs) ⟨s₂, {}, [.trap]⟩) :=
  invoke_obs_of_frame hs hoka hokb hS hW hts hfa htya hfb htyb hrs
    (Abstract.FunctorP.frameXP_run_eq hfa hca htya hfb hcb htyb hmod hloc hbody)

end Silmaril.Wasm.Interp.FunctorP
