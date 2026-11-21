module

public import Silmaril.Wasm.V1.Intrinsic.Scalar.Defs
public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Versions.Thms
import Silmaril.Proofs.Wasm.V1.Intrinsic.Scalar.Thms

@[expose] public section

namespace Silmaril.Wasm.V1.Intrinsic.Scalar

theorem Instr.sound {ctx inputs outputs} (term : Instr ctx inputs outputs) :
    Validation.InstrType ctx term.erase inputs outputs :=
  Proofs.Wasm.V1.Intrinsic.Scalar.instr_sound term

theorem Body.sound {ctx inputs outputs} (term : Body ctx inputs outputs) :
    Validation.ExprType ctx term.erase inputs outputs :=
  Proofs.Wasm.V1.Intrinsic.Scalar.body_sound term

theorem Body.toCore_eq {ctx inputs outputs} (term : Body ctx inputs outputs) :
    term.toCore = Expr.toCore term.erase :=
  Proofs.Wasm.V1.Intrinsic.Scalar.body_toCore term

theorem Function.sound {ctx type sig} (term : Function ctx type sig) :
    Profiles.HasTyping.funcOk (W := Profiles.Wasm1) ctx term.erase sig :=
  ⟨term.resolved, term.singleResult, term.body.sound⟩

theorem Function.toCore_eq {ctx type sig} (term : Function ctx type sig) :
    term.toCore = term.erase.toCore := by
  simp only [Function.toCore, Function.erase, Func.toCore, Func.body, term.body.toCore_eq]

@[simp] theorem ClosedModule.erase_context {sig} (term : ClosedModule sig) :
    Validation.moduleContext term.erase = closedContext sig := rfl

theorem ClosedModule.sound {sig} (term : ClosedModule sig) :
    Profiles.HasTyping.moduleOk (W := Profiles.Wasm1) term.erase () :=
  Proofs.Wasm.V1.Intrinsic.Scalar.closedModule_sound term

theorem ClosedModule.toCore_eq {sig} (term : ClosedModule sig) :
    term.toCore = term.erase.toCore := by
  simp only [ClosedModule.toCore, ClosedModule.erase, Wasm.Scalar.Module.ofFunction, Module.toCore,
    List.map_cons, List.map_nil, term.fn.toCore_eq]
  rfl

theorem ClosedModule.core_sound {sig} (term : ClosedModule sig) :
    Wasm.Validation.ModuleValid term.toCore := by
  rw [term.toCore_eq]
  exact Validation.ModuleValid.toCore term.sound

@[simp] theorem ClosedModule.ofCore?_toCore {sig} (term : ClosedModule sig) :
    V1.Module.ofCore? term.toCore = some term.erase := by
  rw [term.toCore_eq, Module.ofCore?_toCore]

/-- The same term can target Lime's native AST and judgment through the existing
V1 embedding; it is not a lifting result for all Lime expressions. -/
theorem ClosedModule.lime_sound {sig} (term : ClosedModule sig) :
    Profiles.HasTyping.moduleOk (W := Profiles.Lime) term.erase.toLime () :=
  Validation.ModuleValid.toLime term.sound

theorem ClosedModule.lime_toCore_eq {sig} (term : ClosedModule sig) :
    term.erase.toLime.toCore = term.toCore := by
  rw [Module.toLime_toCore, term.toCore_eq]

end Silmaril.Wasm.V1.Intrinsic.Scalar
