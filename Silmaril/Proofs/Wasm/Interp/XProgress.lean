module

public import Silmaril.Proofs.Wasm.Interp.XDivCoreT
public import Silmaril.Proofs.Wasm.Interp.Total

/-!
# Typed progress for the extended semantics (proofs, first part)

Towards `EvalDivX` for typed problems with no closed extended outcome (the extended analog of
`bad_le_evalDiv`):

* `calleeX_flow`: a typed callee's closed answer returns, traps or throws: it never ends in a
  branch past its body (the arity invariant of its body run, as `callee_flow`).
* `WasmFuncs`: every function of the store is Wasm code (a host callee has no closed answer
  and no closed divergence: Core is stuck there), kept by the closure (`wasmFuncs_of_funcs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Wasm.Abstract.XDiverge

variable {H : Type} {P : Numerics.Profile}

/-- Every function of the store is Wasm code. -/
def WasmFuncs (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H), s.funcs[a]? = some fi → ∃ fn, fi.code = .wasm fn

theorem wasmFuncs_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hW : WasmFuncs s) :
    WasmFuncs s' :=
  fun a fi hfi => hW a fi (h ▸ hfi)

include P in
/-- **A typed callee's closed answer returns, traps or throws.** -/
theorem calleeX_flow {s s' : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {fl : Binaryen.Flow} (hS : StoreChkE tExt s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hE : TypedEntry s a us) (h : closedCallX s a us (s', fl)) :
    (∃ vs, fl.retVals = some vs) ∨ fl = .trap ∨ ∃ t, fl = .throw t := by
  rw [closedCallX_fixpoint] at h
  obtain ⟨fi', fn', ps', rs', f₂, hfi', hcode', hty', d⟩ := h
  rw [hfi] at hfi'; cases hfi'
  rw [hcode] at hcode'; cases hcode'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  have ht := callee_typedT hS hE hfi hcode hty hn
  obtain ⟨hA, -⟩ := evalOX_closed_typed_goodT (P := P) d ht
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, -⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  obtain ⟨hok, -⟩ := hA hS (by rw [hlen]; exact hb)
  exact callee_flow hok

end Silmaril.Wasm.Interp
