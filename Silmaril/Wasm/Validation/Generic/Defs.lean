module

public import Silmaril.Wasm.Validation.Inductive.Thms

/-! Function payloads can vary without changing Core declarations or index
order. Typed payload maps preserve the entire context and closed signature.
Initializers outside functions still use Core instructions. -/

@[expose] public section

namespace Silmaril.Wasm.Generic

/-- Core function headers over any expression representation. `Declaration.Func`
already also allows a different representation for local value types. -/
abbrev Function (Body : Type) := Declaration.Func ValType Body

structure RawModule (F : Type) where
  metadata : Wasm.Module
  noFunctions : metadata.funcs = []
  defs : List F

def RawModule.map {F G : Type} (f : F → G) (mod : RawModule F) : RawModule G :=
  ⟨mod.metadata, mod.noFunctions, mod.defs.map f⟩

/-- A partial body translation fails for the whole module if any function fails. -/
def RawModule.traverse {M : Type → Type} [Monad M] {F G : Type}
    (f : F → M G) (mod : RawModule F) : M (RawModule G) :=
  (fun defs => ⟨mod.metadata, mod.noFunctions, defs⟩) <$> mod.defs.mapM f

def RawModule.ofCore (mod : Wasm.Module) : RawModule Wasm.Func :=
  ⟨{ mod with funcs := [] }, rfl, mod.funcs⟩

def RawModule.toCore (mod : RawModule Wasm.Func) : Wasm.Module :=
  { mod.metadata with funcs := mod.defs }

def RawModule.mapInstructions {I J : Type} (f : I → J) (mod : RawModule (Function (List I))) :
    RawModule (Function (List J)) := mod.map (Declaration.Func.mapBody (List.map f))

namespace Typed

open Validation

abbrev BodyFamily := Context → InstrType → Type
abbrev FunctionFamily := Context → DefType → Type

variable {context : Context} {type : DefType} {types : List DefType} {interface : CModuleType}

structure Function (Body : BodyFamily) (context : Context) (type : DefType) where
  typeRef : Inductive.Bounded context.types type
  params : Ty (.list .val)
  results : Ty (.list .val)
  expands : Expand type (.func params results)
  locals : List ValType
  localTypes : List LocalType
  localValid : List.Forall₂ (LocalOk context) locals localTypes
  body : Body (context.funcBody params.toList results.toList localTypes) (.plain [] results.toList)

def Function.map {B C : BodyFamily} (f : ∀ {context sig}, B context sig → C context sig)
    {context type} (fn : Function B context type) : Function C context type :=
  ⟨fn.typeRef, fn.params, fn.results, fn.expands, fn.locals, fn.localTypes, fn.localValid, f fn.body⟩

def Function.erase {context type} (fn : Function Intrinsic.Body context type) : Wasm.Func :=
  let ref : Intrinsic.Ref .type_ context.types type := fn.typeRef.erase
  ⟨ref.index, fn.locals, fn.body.erase⟩

def Function.ofIntrinsic (fn : Intrinsic.Function context type) : Function Intrinsic.Body context type :=
  ⟨Inductive.Bounded.ofRef (kind := .type_) ⟨fn.typeIndex, fn.resolves⟩, fn.params, fn.results,
    fn.expands, fn.locals, fn.localTypes, fn.localValid, fn.body⟩

def Function.toIntrinsic (fn : Function Intrinsic.Body context type) : Intrinsic.Function context type :=
  let ref : Intrinsic.Ref .type_ context.types type := fn.typeRef.erase
  ⟨ref.index, ref.resolves, fn.params, fn.results, fn.expands, fn.locals, fn.localTypes, fn.localValid, fn.body⟩

inductive Definitions (F : FunctionFamily) (context : Context) : List DefType → Type where
  | nil : Definitions F context []
  | cons {type : DefType} {types : List DefType} :
      F context type → Definitions F context types → Definitions F context (type :: types)

def Definitions.map {F G : FunctionFamily} (f : ∀ {context type}, F context type → G context type)
    {context : Context} : {types : List DefType} → Definitions F context types → Definitions G context types
  | _, .nil => .nil
  | _, .cons head tail => .cons (f head) (tail.map f)

/-- A reference into the defined (not imported) slots selects a body at exactly
its declared type. It is not itself a combined Wasm function index. -/
def Definitions.get {F : FunctionFamily} {context : Context} : {types : List DefType} →
    Definitions F context types → Inductive.Path types type → F context type
  | _, .cons head _, .here => head
  | _, .cons _ tail, .there path => tail.get path

def Definitions.toList {F : FunctionFamily} {A : Type} (f : ∀ {context type}, F context type → A)
    {context : Context} : {types : List DefType} → Definitions F context types → List A
  | _, .nil => []
  | _, .cons head tail => f head :: tail.toList f

def Definitions.ofIntrinsic {context : Context} : {types : List DefType} → Intrinsic.Functions context types →
    Definitions (Function Intrinsic.Body) context types
  | _, .nil => .nil
  | _, .cons head tail => .cons (Function.ofIntrinsic head) (ofIntrinsic tail)

def Definitions.toIntrinsic {context : Context} : {types : List DefType} →
    Definitions (Function Intrinsic.Body) context types → Intrinsic.Functions context types
  | _, .nil => .nil
  | _, .cons head tail => .cons (Function.toIntrinsic head) (toIntrinsic tail)

def baseContext (metadata : Wasm.Module) (interface : CModuleType)
    (types funcs : List DefType) : Context :=
  { types := types, globals := CExternType.globals interface.imports
    funcs := CExternType.funcs interface.imports ++ funcs, refs := funcIdxNonFuncs metadata }

def moduleContext (metadata : Wasm.Module) (interface : CModuleType) (types funcs tags : List DefType)
    (globals : List CGlobalType) (tables : List CTableType) (elems : List CRefType) : Context :=
  let base := baseContext metadata interface types funcs
  { base with
    tags := CExternType.tags interface.imports ++ tags, globals := base.globals ++ globals,
    mems := CExternType.mems interface.imports ++ metadata.memories,
    tables := CExternType.tables interface.imports ++ tables,
    datas := metadata.data.map fun _ => (), elems := elems }

/-- Declaration pass. The scope is computed from real Core validation inputs,
including the entire signature table. Definitions are not yet present. -/
structure Header (interface : CModuleType) where
  metadata : Wasm.Module
  noFunctions : metadata.funcs = []
  types : List DefType
  signatures : List DefType
  tags : List DefType
  globals : List CGlobalType
  tables : List CTableType
  elems : List CRefType
  typesValid : TypesOk {} metadata.types types
  importsValid : List.Forall₂ (ImportOk { types := types }) metadata.imports interface.imports
  tagsValid : List.Forall₂ (TagOk (baseContext metadata interface types signatures)) metadata.tags tags
  globalsValid : GlobalsOk (baseContext metadata interface types signatures) metadata.globals globals
  memoriesValid : ∀ memory ∈ metadata.memories, MemOk memory
  tablesValid : List.Forall₂ (TableOk (baseContext metadata interface types signatures)) metadata.tables tables
  dataValid : ∀ data ∈ metadata.data, DataOk (moduleContext metadata interface types signatures tags globals tables elems) data
  elemsValid : List.Forall₂ (ElemOk (moduleContext metadata interface types signatures tags globals tables elems)) metadata.elems elems
  startValid : ∀ index, metadata.start = some index →
    StartOk (moduleContext metadata interface types signatures tags globals tables elems) index
  exportsValid : List.Forall₂ (ExportOk (moduleContext metadata interface types signatures tags globals tables elems))
    metadata.exports interface.exports
  exportsDisjoint : (metadata.exports.map Export.name).Nodup

def Header.scope {interface} (head : Header interface) : Context :=
  moduleContext head.metadata interface head.types head.signatures head.tags head.globals head.tables head.elems

/-- Bodies form a dependent spine in the same declared environment; the tail
does not shrink the call scope. Imported, forward and self references remain in scope. -/
structure Module (F : FunctionFamily) (interface : CModuleType) where
  header : Header interface
  defs : Definitions F header.scope header.signatures

def Module.map {F G : FunctionFamily} (f : ∀ {context type}, F context type → G context type)
    {interface} (mod : Module F interface) : Module G interface :=
  ⟨mod.header, mod.defs.map f⟩

def Module.forget {F : FunctionFamily} {A : Type} (f : ∀ {context type}, F context type → A)
    (mod : Module F interface) : RawModule A :=
  ⟨mod.header.metadata, mod.header.noFunctions, mod.defs.toList f⟩

def Module.erase {interface} (mod : Module (Function Intrinsic.Body) interface) : Wasm.Module :=
  { mod.header.metadata with funcs := mod.defs.toList Function.erase }

def Module.toIntrinsic (mod : Module (Function Intrinsic.Body) interface) : Intrinsic.Module interface :=
  { metadata := mod.header.metadata
    noRawFunctions := mod.header.noFunctions
    definedTypes := mod.header.types
    definedTags := mod.header.tags
    definedGlobals := mod.header.globals
    definedTables := mod.header.tables
    definedFuncs := mod.header.signatures
    elementTypes := mod.header.elems
    baseContext := baseContext mod.header.metadata interface mod.header.types mod.header.signatures
    context := mod.header.scope
    typesValid := mod.header.typesValid
    importsValid := mod.header.importsValid
    baseContextEq := rfl
    contextEq := rfl
    tagsValid := mod.header.tagsValid
    globalsValid := mod.header.globalsValid
    memoriesValid := mod.header.memoriesValid
    tablesValid := mod.header.tablesValid
    funcs := mod.defs.toIntrinsic
    dataValid := mod.header.dataValid
    elemsValid := mod.header.elemsValid
    startValid := mod.header.startValid
    exportsValid := mod.header.exportsValid
    exportsDisjoint := mod.header.exportsDisjoint }

def Module.ofIntrinsic (mod : Intrinsic.Module interface) : Module (Function Intrinsic.Body) interface :=
  match mod with
  | ⟨metadata, noFunctions, types, tags, globals, tables, signatures, elems, _, _, typesValid,
      importsValid, rfl, rfl, tagsValid, globalsValid, memoriesValid, tablesValid, defs,
      dataValid, elemsValid, startValid, exportsValid, exportsDisjoint⟩ =>
    ⟨⟨metadata, noFunctions, types, signatures, tags, globals, tables, elems, typesValid, importsValid,
      tagsValid, globalsValid, memoriesValid, tablesValid, dataValid, elemsValid, startValid,
      exportsValid, exportsDisjoint⟩, Definitions.ofIntrinsic defs⟩

end Typed
end Silmaril.Wasm.Generic
