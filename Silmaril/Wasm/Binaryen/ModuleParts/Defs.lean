module

public import Silmaril.Wasm.Binaryen.Lower
public import Silmaril.Wasm.ModuleParts.Defs

@[expose] public section

namespace Silmaril.Wasm.Binaryen

/-- Compatibility with Binaryen's existing `BModule`, whose `base.funcs`
is ignored when lowering. The assembled empty list is not separately checked. -/
def BModule.ofParts (parts : ModuleParts BFunc) : BModule :=
  ⟨parts.sections.assemble [], parts.defs⟩

def BModule.toParts (mod : BModule) : ModuleParts BFunc := ⟨mod.base.sections, mod.funcs⟩

end Silmaril.Wasm.Binaryen
