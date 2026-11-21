module

public import Silmaril.Wasm.V1.Intrinsic.Scalar.Defs

public section

namespace Silmaril.Proofs.Wasm.V1.Intrinsic.Scalar

open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Validation Silmaril.Wasm.V1.Intrinsic.Scalar

theorem instr_sound {ctx inputs outputs} (term : Instr ctx inputs outputs) :
    InstrType ctx term.erase inputs outputs := by
  cases term with
  | intConst width bits => exact .intConst width bits
  | intBinOp width op => exact .intBinOp width op
  | intRelOp width op => exact .intRelOp width op
  | select ty => exact .select ty
  | localGet idx resolved => exact .localGet idx resolved
  | localSet idx resolved => exact .localSet idx resolved
  | call idx resolved => exact .call idx resolved

theorem body_sound {ctx inputs outputs} (term : Body ctx inputs outputs) :
    ExprType ctx term.erase inputs outputs := by
  induction term with
  | nil stack => exact .nil stack
  | step pre head _ ih => exact .cons (.frame pre (instr_sound head)) ih

theorem body_toCore {ctx inputs outputs} (term : Body ctx inputs outputs) :
    term.toCore = Expr.toCore term.erase := by
  induction term with
  | nil => rfl
  | step _ _ _ ih => simp only [Body.toCore, Body.erase, Expr.toCore, ih]

theorem closedModule_sound {sig} (term : ClosedModule sig) : ModuleValid term.erase where
  types := by
    intro ft hft
    have eq : ft = sig := List.mem_singleton.mp hft
    exact eq ▸ term.fn.singleResult
  imports := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  functions := by
    intro fn hfn
    have eq : fn = term.fn.erase := List.mem_singleton.mp hfn
    subst fn
    exact ⟨sig, term.fn.resolved, term.fn.singleResult, body_sound term.fn.body⟩
  tables := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  memories := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  globals := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  elements := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  data := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  start := by simp [StartValid, ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  exports := by
    intro exp hexp
    have eq : exp = ⟨term.exportName, .func ⟨0⟩⟩ := List.mem_singleton.mp hexp
    subst exp
    exact ⟨.func sig, rfl⟩
  uniqueExports := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  singleTable := Nat.zero_le _
  singleMemory := Nat.zero_le _

end Silmaril.Proofs.Wasm.V1.Intrinsic.Scalar
