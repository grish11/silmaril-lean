module

public import Silmaril.Wasm.Modules

@[expose] public section

namespace Silmaril.Wasm

namespace Declaration

/-- The type use and additional locals of a defined function. Its parameter
types come from the module's type context, not from the local declarations. -/
structure FuncDecl (V : Type) where
  type : TypeIdx
  locals : List V
  deriving Repr

variable {V B : Type}

def Func.declaration (fn : Func V B) : FuncDecl V := ⟨fn.type, fn.locals⟩

def FuncDecl.withBody (decl : FuncDecl V) (body : B) : Func V B := ⟨decl.type, decl.locals, body⟩

def Func.split (fn : Func V B) : FuncDecl V × B := (fn.declaration, fn.body)

end Declaration

/-- Everything in a Core module except the local function definitions. This
includes executable initializers and references into the module's function
index space. It is section data, not a valid standalone module. -/
structure ModuleSections where
  types : List RecType := []
  imports : List Import := []
  tags : List TagType := []
  globals : List Global := []
  memories : List MemoryType := []
  tables : List Table := []
  data : List Data := []
  elems : List Elem := []
  start : Option FuncIdx := none
  exports : List Export := []
  deriving Repr

def Module.sections (mod : Module) : ModuleSections :=
  ⟨mod.types, mod.imports, mod.tags, mod.globals, mod.memories, mod.tables, mod.data, mod.elems, mod.start, mod.exports⟩

def ModuleSections.assemble (secs : ModuleSections) (defs : List Func) : Module :=
  ⟨secs.types, secs.imports, secs.tags, secs.globals, secs.memories, secs.tables, defs, secs.data,
    secs.elems, secs.start, secs.exports⟩

def ModuleSections.typeDefinitions (secs : ModuleSections) : List SubType :=
  secs.types.flatMap RecType.types

def ModuleSections.importedFunctions (secs : ModuleSections) : List TypeIdx :=
  secs.imports.filterMap fun entry => match entry.type with
    | .func type => some type
    | _ => none

/-- The supplied type uses are those of the local definitions. Imports are
counted first in the combined function index space. -/
def ModuleSections.functionTypes (secs : ModuleSections) (defined : List TypeIdx) : List TypeIdx :=
  secs.importedFunctions ++ defined

structure ModuleParts (F : Type) where
  sections : ModuleSections
  defs : List F
  deriving Repr

def Module.split (mod : Module) : ModuleParts Func := ⟨mod.sections, mod.funcs⟩

def ModuleParts.toCore (parts : ModuleParts Func) : Module := parts.sections.assemble parts.defs

def ModuleParts.map {F G : Type} (f : F → G) (parts : ModuleParts F) : ModuleParts G :=
  ⟨parts.sections, parts.defs.map f⟩

/-- Map each function's instruction list, without visiting section expressions. -/
def ModuleParts.mapInstructions {V I J : Type} (f : I → J) (parts : ModuleParts (Declaration.Func V (List I))) :
    ModuleParts (Declaration.Func V (List J)) := parts.map (Declaration.Func.mapBody (List.map f))

/-- A partial body translation fails for the whole module if any function fails. -/
def ModuleParts.traverse {M : Type → Type} [Monad M] {F G : Type} (f : F → M G)
    (parts : ModuleParts F) : M (ModuleParts G) :=
  ModuleParts.mk parts.sections <$> parts.defs.mapM f

def ModuleParts.functionDecls {V B : Type} (parts : ModuleParts (Declaration.Func V B)) :
    List (Declaration.FuncDecl V) := parts.defs.map Declaration.Func.declaration

def Module.functionDecls (mod : Module) : List (Declaration.FuncDecl ValType) := mod.split.functionDecls

def Module.functionBodies (mod : Module) : List Expr := mod.funcs.map Func.body

def ModuleParts.functionTypes {V B : Type} (parts : ModuleParts (Declaration.Func V B)) : List TypeIdx :=
  parts.sections.functionTypes (parts.defs.map Declaration.Func.type)

/-- Resolve a function's type use against the actual type section. This is a
syntactic query: it does not close types or validate the module. -/
def ModuleParts.functionSignature? {V B : Type} (parts : ModuleParts (Declaration.Func V B))
    (index : FuncIdx) : Option FuncType := do
  let type ← parts.functionTypes[index.toNat]?
  match parts.sections.typeDefinitions[type.toNat]? with
  | some ⟨_, _, .func signature⟩ => some signature
  | _ => none

def Module.functionSignature? (mod : Module) (index : FuncIdx) : Option FuncType :=
  mod.split.functionSignature? index

end Silmaril.Wasm
