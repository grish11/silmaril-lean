module

public import Silmaril.Wasm.Abstract.CallXT.Defs
import Silmaril.Proofs.Wasm.Abstract.CallXT.Basic
import Silmaril.Proofs.Wasm.Abstract.CallXT.Typed
import Silmaril.Proofs.Wasm.Abstract.CallXT.RefSite
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
# The extended relation with typed callee arities: theorems

* `EvalOXT.forget`: every `EvalOXT C` run is an `EvalOX C` run with the same
  outcome. The arity premises only strengthen the derivation.
* `evalOXT_iff_evalOX`: on code without indirect or reference calls, tail
  forms included (`irFreeL`), the two are the same.

* **Counts from reference typing.** `typeArity_of_refOk`: a function reference
  typed (`RefOk`) at `ref null? y`, for a valid `y`, has the parameter and
  result counts of `y`. A reference's typing chain composes, and subtyping of
  defined function types keeps counts. `typeArity_of_cast`: the successful
  `ref.cast` of `call_indirect` types the callee so.
* **The `call_indirect` premise from typing.** `evalOXT_of_evalOX_ind`: with
  valid function types (`TyFuncs`) and instance types (`TyTypes`), code
  without `call_ref`/`return_call_ref` whose (tail) indirect calls name
  instance types (`indOkL`) runs in `EvalOXT` whenever it runs in `EvalOX`, for an oracle keeping function
  types valid; `evalOXT_of_evalOX_closed` for `XRecursion.closedCallX`.

* **The `call_ref` premise at a typed site.** `typeArity_of_callRef_site`: if
  the Core configuration at `call_ref y` on a function reference is typed in
  context (`Sim.ContextTyped`), the referenced function has the counts of `y`.

**Not yet.** Carrying `ContextTyped` along `EvalOX` runs (Core preservation of
the arguments' Core runs), which turns the site lemma into the `call_ref`
premise for whole runs.
-/

public section

namespace Silmaril.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX

variable {H : Type}

/-- **Forgetting the arity premises.** -/
theorem EvalOXT.forget {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOXT C s f stk es r) :
    EvalOX C s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.forget h

/-- **Conservativity.** Without indirect and reference calls, the arity premises
are vacuous. -/
theorem evalOXT_iff_evalOX {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (hx : irFreeL es = true) :
    EvalOXT C s f stk es r ↔ EvalOX C s f stk es r :=
  ⟨EvalOXT.forget, fun h => Silmaril.Proofs.Wasm.Abstract.CallXT.of_irFree h hx⟩

open Silmaril.Wasm.Validation (TyOk DefType CValType)

/-- **A function reference typed at `ref null? y` has the counts of `y`.** -/
theorem typeArity_of_refOk {s : Store H} {a : Nat} {fi : FuncInst H} {mi : ModuleInst}
    {y : TypeIdx} {d : DefType} {n : Bool} {ps rs : List CValType}
    (hd : mi.types[y.toNat]? = some d) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) (hdok : TyOk {} d)
    (h : RefOk s (.func a) (.ref n (.use (.dt d)))) :
    typeArity mi y = some (ps.length, rs.length) :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.typeArity_of_refOk hd hfi hty hfiok hdok h

/-- **The cast of `call_indirect` gives the callee the counts of `y`.** -/
theorem typeArity_of_cast {s : Store H} {a : Nat} {fi : FuncInst H} {mi : ModuleInst}
    {y : TypeIdx} {d : DefType} {ps rs : List CValType}
    (hd : mi.types[y.toNat]? = some d) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) (hdok : TyOk {} d)
    (h : RefOk s (.func a) (mi.instRef (Silmaril.Wasm.Abstract.CallRes.castTo y))) :
    typeArity mi y = some (ps.length, rs.length) :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.typeArity_of_cast hd hfi hty hfiok hdok h

/-- **The `call_indirect` premise from typing.** -/
theorem evalOXT_of_evalOX_ind {C : CallRel H} (hC : KeepsTy C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r)
    (hs : TyFuncs s) (hm : TyTypes f.module) (hx : indOkL f.module es = true) :
    EvalOXT C s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.evalOXT_of_evalOX_ind hC h hs hm hx

theorem closedCallX_keepsTy : KeepsTy (Silmaril.Wasm.Abstract.XRecursion.closedCallX : CallRel H) :=
  fun _ _ _ _ h hs a fi hfi =>
    hs a fi (Silmaril.Wasm.Abstract.XRecursion.closedCallX_funcs h ▸ hfi)

/-- The closed instance. -/
theorem evalOXT_of_evalOX_closed {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow}
    (h : EvalOX Silmaril.Wasm.Abstract.XRecursion.closedCallX s f stk es r)
    (hs : TyFuncs s) (hm : TyTypes f.module) (hx : indOkL f.module es = true) :
    EvalOXT Silmaril.Wasm.Abstract.XRecursion.closedCallX s f stk es r :=
  evalOXT_of_evalOX_ind closedCallX_keepsTy h hs hm hx

/-- **The `call_ref` premise at a typed site.** -/
theorem typeArity_of_callRef_site {s : Store H} {f : Frame} {stk : List Val} {fa : Nat}
    {y : TypeIdx} {rest : List Admin} {fi : FuncInst H} {ps rs : List CValType}
    (ht : Silmaril.Wasm.Execution.Core.Sim.ContextTyped
      ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest⟩)
    (hm : TyTypes f.module) (hfi : s.funcs[fa]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) :
    typeArity f.module y = some (ps.length, rs.length) :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.typeArity_of_callRef_site ht hm hfi hty hfiok

/-- Runs keep the frame's instance. -/
theorem evalOX_module {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    r.2.1.module = f.module :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.evalOX_module h

/-- Runs keep function types valid, when their oracle does. -/
theorem evalOX_tyFuncs {C : CallRel H} (hC : KeepsTy C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r)
    (hs : TyFuncs s) : TyFuncs r.1 :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.evalOX_tyFuncs hC h hs

/-- The arity premise of a resolved indirect call, from its cast. -/
theorem typeArity_of_indRes {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType}
    {i : BitVec ad.intType.width} {fa : Nat} {fi : FuncInst H} {ps rs : List CValType}
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s f x y ad i (some fa))
    (hfi : s.funcs[fa]? = some fi) (hty : DefType.funcType? fi.type = some (ps, rs))
    (hs : TyFuncs s) (hm : TyTypes f.module) (hy : (f.module.types[y.toNat]?).isSome = true) :
    typeArity f.module y = some (ps.length, rs.length) :=
  Silmaril.Proofs.Wasm.Abstract.CallXT.typeArity_of_indRes hres hfi hty hs hm hy

end Silmaril.Wasm.Abstract.CallXT
