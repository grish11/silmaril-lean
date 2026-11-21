module

public import Silmaril.Wasm.Validation.ModuleParts.Defs
public import Silmaril.Wasm.ModuleParts.Thms
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace Silmaril.Wasm

open Validation

@[simp] theorem Validation.sectionFuncRefs_sections (mod : Module) :
    sectionFuncRefs mod.sections = funcIdxNonFuncs mod := rfl

@[simp] theorem Validation.sectionBaseContext_sections (mod : Module) (types : List DefType)
    (imports : List CExternType) (signatures : List DefType) :
    sectionBaseContext mod.sections types imports signatures = moduleCtx' mod types imports signatures := rfl

@[simp] theorem Validation.sectionContext_sections (mod : Module) (base : Context) (imports : List CExternType)
    (tags : List DefType) (globals : List CGlobalType) (tables : List CTableType) (elems : List CRefType) :
    sectionContext mod.sections base imports tags globals tables elems =
      moduleCtx mod base imports tags globals tables elems := rfl

/-- Resolve and validate the actual Core interface, only after the function
definitions and all other sections have been assembled. -/
def ModuleParts.validate? (parts : ModuleParts Func) : Option CModuleType := Validation.validate? parts.toCore

theorem ModuleParts.validate?_sound {parts : ModuleParts Func} {interface : CModuleType}
    (checked : parts.validate? = some interface) : ModuleOk parts.toCore interface := Validation.validate?_sound checked

end Silmaril.Wasm
