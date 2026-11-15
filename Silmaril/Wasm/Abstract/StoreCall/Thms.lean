module

public import Silmaril.Wasm.Abstract.StoreCall.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Abstract.Oracle.Thms
import Silmaril.Proofs.Wasm.Abstract.StoreCall.Expose

/-!
# Store bodies with internal calls as events: theorems (F4, exposure)

For the exposed abstract body `denListE = denListC callEv`
(`Silmaril.Wasm.Abstract.StoreCall.Defs`), whose internal calls are visible
events of `CallSig H`:

* **Exposure is sound for `EvalO`.** `evalO_path`: every derivation of the
  oracle semantics `Recursion.EvalO C` is a path of the exposed abstract body
  whose call events are all answered as `C` allows (`Answered C`), ending as
  the derivation does (`endR`; a trap is the trap effect).
* **Recursion closed.** `eval_path`: every derivation of the native
  interpreter's recursive big-step relation `Binaryen.Eval` (calls run their
  callees) is such a path with the answers of the closure `closedCall`
  (`Recursion.evalO_closed_iff`).
* **Core 3.0.** `core_call_path`: on typed, native, arity-checked stores at
  every profile, every Core 3.0 run of an invocation to a result with final
  store `s'`, internal calls and recursion included, is an answered path of
  the exposed abstract body of the callee's code, with the answers of
  `closedCall`, which is Core 3.0's call semantics (`Oracle.closedCall_core_iff`).

**Not yet.** The converse (every answered path is an `EvalO` derivation),
divergence through calls, `try_table` (F5) and imports (host events).
-/

public section

namespace Silmaril.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody

variable {H : Type}

/-- **Exposure.** Every `EvalO C` derivation is a path of the exposed abstract
body with every call event answered by `C`. -/
theorem evalO_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) :
    ∃ cs, Answered C cs ∧
      Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (endR r) :=
  Silmaril.Proofs.Wasm.Abstract.StoreCall.evalO_path h

/-- **Recursion.** Every derivation of the recursive native semantics is a path
of the exposed abstract body with every call answered by the closure. -/
theorem eval_path {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) :
    ∃ cs, Answered closedCall cs ∧
      Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (endR r) :=
  evalO_path (evalO_closed_iff.2 h)

/-- **Core 3.0, with calls and recursion.** Every Core run of an invocation to a
result is an answered path of the exposed abstract body of the callee, with the
answers of `closedCall` (Core's call semantics). -/
theorem core_call_path {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) (r : Result) (s' : Store H)
    (h : ∃ c : Config H, Steps P closedHost (invoke s a us) c ∧ c.code = r.toAdmin ∧
      c.store = s') :
    ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (f₂ : Frame)
      (bfl fl : Flow) (cs : List (Call (CallSig H))),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      Answered closedCall cs ∧
      Path (((denListE (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) [] :
        M (CallSig H) H Res).run ⟨s⟩).run) cs (endR (s', f₂, bfl)) ∧
      exitFlow rs.length bfl = some fl ∧ flowBeh fl = some r.toBehaviour := by
  obtain ⟨fi, ps, rs, bfl, fl, hfi, hty, hc, hex, hb⟩ :=
    (closedCall_core_iff hs hF hS hok P r s').2 h
  rw [closedCall_fixpoint] at hc
  obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hev⟩ := hc
  rw [hfi] at hfi'
  obtain rfl := Option.some.inj hfi'
  rw [hty] at hty'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty')
  obtain ⟨cs, hA, hp⟩ := evalO_path hev
  exact ⟨fi, fn, ps, rs, f₂, bfl, fl, cs, hfi, hcode, hty, hA, hp, hex, hb⟩

end Silmaril.Wasm.Abstract.StoreCall
