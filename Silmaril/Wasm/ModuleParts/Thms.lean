module

public import Silmaril.Wasm.ModuleParts.Defs

public section

namespace Silmaril.Wasm

namespace Declaration

@[simp] theorem Func.withBody_split {V B : Type} (fn : Func V B) : fn.split.1.withBody fn.split.2 = fn :=
  by cases fn; rfl

@[simp] theorem FuncDecl.split_withBody {V B : Type} (decl : FuncDecl V) (body : B) :
    (decl.withBody body).split = (decl, body) := by cases decl; rfl

def Func.splitEquiv {V B : Type} : Func V B ≃ FuncDecl V × B where
  toFun := Func.split
  invFun parts := parts.1.withBody parts.2
  left_inv := Func.withBody_split
  right_inv parts := FuncDecl.split_withBody parts.1 parts.2

@[simp] theorem Func.declaration_mapBody {V B C : Type} (f : B → C) (fn : Func V B) :
    (fn.mapBody f).declaration = fn.declaration := rfl

theorem Func.split_mapBody {V B C : Type} (f : B → C) (fn : Func V B) :
    (fn.mapBody f).split = (fn.split.1, f fn.split.2) := rfl

end Declaration

@[simp] theorem ModuleSections.sections_assemble (secs : ModuleSections) (defs : List Func) :
    (secs.assemble defs).sections = secs := by cases secs; rfl

@[simp] theorem Module.assemble_sections (mod : Module) : mod.sections.assemble mod.funcs = mod :=
  by cases mod; rfl

@[simp] theorem Module.toCore_split (mod : Module) : mod.split.toCore = mod := mod.assemble_sections

@[simp] theorem ModuleParts.split_toCore (parts : ModuleParts Func) : parts.toCore.split = parts :=
  by cases parts with | mk secs defs => cases secs; rfl

def Module.splitEquiv : Module ≃ ModuleParts Func where
  toFun := Module.split
  invFun := ModuleParts.toCore
  left_inv := Module.toCore_split
  right_inv := ModuleParts.split_toCore

theorem Module.split_injective : Function.Injective split := splitEquiv.injective

theorem ModuleParts.toCore_injective : Function.Injective toCore := Module.splitEquiv.symm.injective

@[simp] theorem ModuleParts.map_id {F : Type} (parts : ModuleParts F) : parts.map id = parts := by
  cases parts; simp [map]

theorem ModuleParts.map_comp {F G K : Type} (f : F → G) (g : G → K) (parts : ModuleParts F) :
    (parts.map f).map g = parts.map (g ∘ f) := by cases parts; simp [map, List.map_map]

@[simp] theorem ModuleParts.sections_map {F G : Type} (f : F → G) (parts : ModuleParts F) :
    (parts.map f).sections = parts.sections := rfl

@[simp] theorem Module.functionTypes_split (mod : Module) : mod.split.functionTypes = mod.functionTypes := rfl

theorem Module.split_mapBody (mod : Module) (f : Expr → Expr) :
    ({ mod with funcs := mod.funcs.map (Declaration.Func.mapBody f) } : Module).split =
      mod.split.map (Declaration.Func.mapBody f) := rfl

@[simp] theorem ModuleParts.functionTypes_mapBody {V B C : Type} (parts : ModuleParts (Declaration.Func V B))
    (f : B → C) : (parts.map (Declaration.Func.mapBody f)).functionTypes = parts.functionTypes := by
  simp [functionTypes, map, List.map_map, Function.comp_def, Declaration.Func.mapBody]

@[simp] theorem ModuleParts.functionDecls_mapBody {V B C : Type} (parts : ModuleParts (Declaration.Func V B))
    (f : B → C) : (parts.map (Declaration.Func.mapBody f)).functionDecls = parts.functionDecls := by
  simp [functionDecls, map, List.map_map, Function.comp_def]

@[simp] theorem ModuleParts.functionSignature?_mapBody {V B C : Type} (parts : ModuleParts (Declaration.Func V B))
    (f : B → C) (index : FuncIdx) : (parts.map (Declaration.Func.mapBody f)).functionSignature? index =
      parts.functionSignature? index := by simp [functionSignature?]

end Silmaril.Wasm
