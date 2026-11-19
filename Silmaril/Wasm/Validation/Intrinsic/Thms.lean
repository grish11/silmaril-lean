module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs
import Silmaril.Proofs.Wasm.Validation.Intrinsic.Typing
import Silmaril.Proofs.Wasm.Validation.Intrinsic.Equiv

/-! Intrinsic and raw terms agree exactly up to erasure. This is not an equivalence of
proof-relevant witnesses: there can be several sequence trees, frames or subtyping steps
for the identical raw expression. The quotient forgets just that extra structure. -/

public section

namespace Silmaril.Wasm.Validation.Intrinsic

theorem Step.sound {context sig} (step : Step context sig) : InstrOk context step.erase sig :=
  Proofs.Wasm.Validation.Intrinsic.step_sound step

theorem Body.sound {context sig} (body : Body context sig) : InstrsOk context body.erase sig :=
  Proofs.Wasm.Validation.Intrinsic.body_sound body

theorem Body.lift_erase {context ops sig} (valid : InstrsOk context ops sig) :
    ∃ body : Body context sig, body.erase = ops :=
  Proofs.Wasm.Validation.Intrinsic.lift_body valid

theorem Function.sound {context type} (func : Function context type) :
    FuncOk context func.erase type := Proofs.Wasm.Validation.Intrinsic.function_sound func

theorem Function.lift_erase {context raw type} (valid : FuncOk context raw type) :
    ∃ func : Function context type, func.erase = raw :=
  Proofs.Wasm.Validation.Intrinsic.lift_function valid

theorem Module.sound {interface} (mod : Module interface) : ModuleOk mod.erase interface :=
  Proofs.Wasm.Validation.Intrinsic.module_sound mod

theorem Module.lift_erase {raw interface} (valid : ModuleOk raw interface) :
    ∃ mod : Module interface, mod.erase = raw := Proofs.Wasm.Validation.Intrinsic.lift_module valid

/-- Equality is exact equality of erased functions, not a behavioral approximation. -/
abbrev Function.Erasure (context : Context) (type : DefType) :=
  Quot (fun left right : Function context type => left.erase = right.erase)

/-- Equality is exact equality of erased modules, including their raw metadata. -/
abbrev Module.Erasure (interface : CModuleType) :=
  Quot (fun left right : Module interface => left.erase = right.erase)

noncomputable def Function.equiv (context : Context) (type : DefType) :
    Function.Erasure context type ≃ { raw // FuncOk context raw type } :=
  Proofs.Wasm.Validation.Intrinsic.erasureEquiv Function.erase Function.sound Function.lift_erase

noncomputable def Module.equiv (interface : CModuleType) :
    Module.Erasure interface ≃ { raw // ModuleOk raw interface } :=
  Proofs.Wasm.Validation.Intrinsic.erasureEquiv Module.erase Module.sound Module.lift_erase

end Silmaril.Wasm.Validation.Intrinsic
