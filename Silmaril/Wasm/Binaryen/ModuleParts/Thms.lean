module

public import Silmaril.Wasm.Binaryen.ModuleParts.Defs
public import Silmaril.Wasm.ModuleParts.Thms

public section

namespace Silmaril.Wasm.Binaryen

@[simp] theorem BModule.toParts_ofParts (parts : ModuleParts BFunc) : (ofParts parts).toParts = parts := by
  cases parts
  simp [ofParts, toParts]

theorem BModule.lower_toParts (mod : BModule) :
    (mod.toParts.map (Declaration.Func.mapBody BExpr.lowerList)).toCore = mod.lower := by
  cases mod with | mk base funcs => cases base; rfl

theorem BModule.lower_ofParts (parts : ModuleParts BFunc) :
    (ofParts parts).lower = (parts.map (Declaration.Func.mapBody BExpr.lowerList)).toCore := by
  simpa only [toParts_ofParts] using (lower_toParts (ofParts parts)).symm

end Silmaril.Wasm.Binaryen
