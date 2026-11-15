module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Interp.HostEvalP.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Direct

/-!
# The canonical relation with host calls as an open module: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingXP`.

* `evalLXPh_of_evalL`: every native logged run `EvalL` is a canonical logged run `EvalLXPh`,
  ending in the same flow; so `wasmHOpen_le_wasmHOpenXP` and `wasmEvFun_le_wasmEvFunXP` (every
  store).
* `wasmEvFunXP_ret_len`: a function returns at most its result arity; so a cut call is never
  resolved by a return.
* **Coincidence on direct stores** (`Interp.StoreDirect`: Wasm bodies without the extended call
  forms and the exception forms):
  * `wasmHOpenXP_direct`: a canonical open behaviour is a native one, or **cut**: it ends in a
    trap, its log ends in a cut call (an answer of more values than the callee's result arity),
    and answering that call by an exception instead (`inr 0`, ending the function in
    `ret (inr 0)`) is a native open behaviour. Cut behaviours are not native ones, so the open
    modules differ exactly by them;
  * `wasmEvFunXP_direct`: the closures agree, on behaviours whose host answers leave direct
    stores (the host answers are arbitrary in a closure: an answer adding a function with a
    `try_table` leaves the direct fragment, where the native module has no behaviour);
  * `wasmEvFunXP_direct_consistent`: so on behaviours whose log a host keeping direct stores
    (`Interp.HostKeepsDirect`) allows.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (StoreDirect)

variable {H : Type}

/-- Every native logged run is a canonical logged run, ending in the same flow. -/
theorem evalLXPh_of_evalL {s s' : Store H} {f f' : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {fl : Flow} (h : EvalL s f stk es l (s', f', fl)) :
    EvalLXPh s f stk es l (s', f', .flow fl) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_of_evalL h

/-- The native open module is included in the canonical one, at every store. -/
theorem wasmHOpen_le_wasmHOpenXP : wasmHOpen (H := H) ≤ wasmHOpenXP :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpen_le

/-- The native closure is included in the canonical one, at every store. -/
theorem wasmEvFun_le_wasmEvFunXP : wasmEvFun (H := H) ≤ wasmEvFunXP :=
  fun s p => Shape.close_mono wasmHOpen_le_wasmHOpenXP p.1 s p.2

/-- **A function returns at most its result arity.** -/
theorem wasmEvFunXP_ret_len {s s' : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s') ∈ wasmEvFunXP s (a, vs)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_ret_len h

/-- **On a direct store, a canonical open behaviour is native, or cut.** -/
theorem wasmHOpenXP_direct {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) :
    x ∈ wasmHOpen a s vs ∨
      (x.2 = .trap ∧ ∃ (pre : List (OCall H)) (a' : Nat) (args : List Val) (s₁ s₂ : Store H)
        (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
        x.1 = (pre ++ [OCall.mk a' args s₁ (.inl ws) s₂]).map OCall.lift ∧
        s₁.funcs[a']? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        rs.length < ws.length ∧
        ((pre ++ [OCall.mk a' args s₁ (.inr 0) s₂]).map OCall.lift, .ret (.inr 0) s₂) ∈
          wasmHOpen a s vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpenXP_direct hs hx

/-- **On direct stores the closures agree**, on behaviours whose host answers leave direct
stores. -/
theorem wasmEvFunXP_direct {s : Store H} {a : Nat} {vs : List Val} (hs : StoreDirect s)
    {cs : List (Call (wasmHostSig H))} (hd : ∀ c ∈ cs, StoreDirect c.2.1)
    {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct hs hd

/-- **On direct stores the closures agree on behaviours a host keeping direct stores allows.** -/
theorem wasmEvFunXP_direct_consistent {host : HostSemantics H}
    (hD : Interp.HostKeepsDirect host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreDirect s) {cs : List (Call (wasmHostSig H))}
    (hc : (coreHostRel host).Consistent cs) {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct_consistent hD hs hc

end Silmaril.Wasm.Abstract
