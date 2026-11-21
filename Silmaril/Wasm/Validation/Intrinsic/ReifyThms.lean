module

public import Silmaril.Wasm.Validation.Intrinsic.Reify
public import Silmaril.Wasm.Validation.Intrinsic.Thms

public section

namespace Silmaril.Wasm.Validation.Intrinsic.Reify

/-- Reification proves the existing module typing judgment for the original raw term. -/
theorem Reified.sound {raw : Wasm.Module} (witness : Reified raw) : ModuleOk raw witness.interface :=
  Eq.mp (congrArg (fun module_ => ModuleOk module_ witness.interface) witness.erase_eq) witness.typed.sound

end Silmaril.Wasm.Validation.Intrinsic.Reify
