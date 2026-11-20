module

public import Silmaril.Wasm.Validation.Modules

/-! A proof-relevant Core syntax. Sequence nodes expose intermediate stack types and local
initialization; block bodies live under extended label contexts. Atomic families without their
own intrinsic constructor carry their existing typing rule, not a second validator. -/

@[expose] public section

namespace Silmaril.Wasm.Validation.Intrinsic

/-- A source index together with what it denotes in its index space. -/
structure Ref (kind : IndexKind) {α : Type} (entries : List α) (value : α) where
  index : Idx kind
  resolves : entries[index.toNat]? = some value

abbrev LocalRef (context : Context) := Ref .local context.locals
abbrev LabelRef (context : Context) := Ref .label context.labels

structure FunctionRef (context : Context) (params results : Ty (.list .val)) where
  type : DefType
  ref : Ref .func context.funcs type
  expands : Expand type (.func params results)

/-- Structured control cannot be smuggled into a proof-carrying atomic leaf. -/
def isAtomic : Instr → Bool
  | .block .. | .loop .. | .if_ .. | .tryTable .. => false
  | _ => true

mutual

inductive Step : Context → InstrType → Type where
  | atom {context sig} (op : Instr) (atomic : isAtomic op = true) (typed : InstrOk context op sig) :
      Step context sig
  | localGet {context type} (ref : LocalRef context ⟨.set, type⟩) :
      Step context (.plain [] [type])
  | localSet {context init type} (ref : LocalRef context ⟨init, type⟩) :
      Step context ⟨[type], [ref.index.toNat], []⟩
  | localTee {context init type} (ref : LocalRef context ⟨init, type⟩) :
      Step context ⟨[type], [ref.index.toNat], [type]⟩
  | call {context params results} (ref : FunctionRef context params results) :
      Step context (.plain params.toList results.toList)
  | br {context target stackPrefix results} (ref : LabelRef context target)
      (stack : InstrTypeOk context (.plain stackPrefix results)) :
      Step context (.plain (stackPrefix ++ target) results)
  | brIf {context target} (ref : LabelRef context target) :
      Step context (.plain (target ++ [.i32]) target)
  | return_ {context target stackPrefix results} (ref : context.return_ = some target)
      (stack : InstrTypeOk context (.plain stackPrefix results)) :
      Step context (.plain (stackPrefix ++ target) results)
  | unreachable {context params results} (stack : InstrTypeOk context (.plain params results)) :
      Step context (.plain params results)
  | block {context params results inits} (type : BlockType) (valid : BlockTypeOk context type params results)
      (body : Body (context.withLabel results) ⟨params, inits, results⟩) :
      Step context (.plain params results)
  | loop {context params results inits} (type : BlockType) (valid : BlockTypeOk context type params results)
      (body : Body (context.withLabel params) ⟨params, inits, results⟩) :
      Step context (.plain params results)
  | if_ {context params results thenInits elseInits} (type : BlockType)
      (valid : BlockTypeOk context type params results)
      (thenBody : Body (context.withLabel results) ⟨params, thenInits, results⟩)
      (elseBody : Body (context.withLabel results) ⟨params, elseInits, results⟩) :
      Step context (.plain (params ++ [.i32]) results)
  | tryTable {context params results inits} (type : BlockType)
      (valid : BlockTypeOk context type params results) (catches : List Catch)
      (catchValid : ∀ entry ∈ catches, CatchOk context entry)
      (body : Body (context.withLabel results) ⟨params, inits, results⟩) :
      Step context (.plain params results)

/-- Stack effects, initialized locals, subtyping, and the preserved stack prefix are explicit. -/
inductive Body : Context → InstrType → Type where
  | nil {context} : Body context (.plain [] [])
  | single {context sig} (step : Step context sig) : Body context sig
  | seq {context input middle output firstInits restInits}
      (first : Body context ⟨input, firstInits, middle⟩)
      (locals : ∀ index ∈ firstInits, ∃ localType, context.locals[index]? = some localType)
      (rest : Body (context.initLocals firstInits) ⟨middle, restInits, output⟩) :
      Body context ⟨input, firstInits ++ restInits, output⟩
  | sub {context sig adjusted} (body : Body context sig) (subtype : InstrTypeSub context sig adjusted)
      (valid : InstrTypeOk context adjusted) : Body context adjusted
  | frame {context stackPrefix input output inits} (body : Body context ⟨input, inits, output⟩)
      (valid : ResultOk context.toTypeCtx stackPrefix) :
      Body context ⟨stackPrefix ++ input, inits, stackPrefix ++ output⟩

end

mutual

def Step.erase {context sig} : Step context sig → Instr
  | .atom op _ _ => op
  | .localGet ref => .localGet ref.index
  | .localSet ref => .localSet ref.index
  | .localTee ref => .localTee ref.index
  | .call ref => .call ref.ref.index
  | .br ref _ => .br ref.index
  | .brIf ref => .brIf ref.index
  | .return_ .. => .return_
  | .unreachable _ => .unreachable
  | .block type _ body => .block type body.erase
  | .loop type _ body => .loop type body.erase
  | .if_ type _ thenBody elseBody => .if_ type thenBody.erase elseBody.erase
  | .tryTable type _ catches _ body => .tryTable type catches body.erase

def Body.erase {context sig} : Body context sig → List Instr
  | .nil => []
  | .single step => [step.erase]
  | .seq first _ rest => first.erase ++ rest.erase
  | .sub body .. | .frame body _ => body.erase

end

/-- The core function's raw type index and local declarations are preserved; its body is not a
raw expression with a proof. It is a typed program under the function's actual body context. -/
structure Function (context : Context) (type : DefType) where
  typeIndex : TypeIdx
  resolves : context.type? typeIndex = some type
  params : Ty (.list .val)
  results : Ty (.list .val)
  expands : Expand type (.func params results)
  locals : List ValType
  localTypes : List LocalType
  localValid : List.Forall₂ (LocalOk context) locals localTypes
  body : Body (context.funcBody params.toList results.toList localTypes) (.plain [] results.toList)

def Function.erase {context type} (func : Function context type) : Wasm.Func :=
  ⟨func.typeIndex, func.locals, func.body.erase⟩

inductive Functions (context : Context) : List DefType → Type where
  | nil : Functions context []
  | cons {type types} (head : Function context type) (tail : Functions context types) :
      Functions context (type :: types)

def Functions.erase {context types} : Functions context types → List Wasm.Func
  | .nil => []
  | .cons head tail => head.erase :: tail.erase

/-- Non-function declarations are retained verbatim. The environment links imports and typed
definitions in Wasm index order, so function references include imported and recursive calls. -/
structure Module (interface : CModuleType) where
  metadata : Wasm.Module
  noRawFunctions : metadata.funcs = []
  definedTypes : List DefType
  definedTags : List DefType
  definedGlobals : List CGlobalType
  definedTables : List CTableType
  definedFuncs : List DefType
  elementTypes : List CRefType
  baseContext : Context
  context : Context
  typesValid : TypesOk {} metadata.types definedTypes
  importsValid : List.Forall₂ (ImportOk { types := definedTypes }) metadata.imports interface.imports
  baseContextEq : baseContext = {
    types := definedTypes, globals := CExternType.globals interface.imports
    funcs := CExternType.funcs interface.imports ++ definedFuncs, refs := funcIdxNonFuncs metadata }
  contextEq : context = { baseContext with
    tags := CExternType.tags interface.imports ++ definedTags, globals := baseContext.globals ++ definedGlobals,
    mems := CExternType.mems interface.imports ++ metadata.memories,
    tables := CExternType.tables interface.imports ++ definedTables,
    datas := metadata.data.map fun _ => (), elems := elementTypes }
  tagsValid : List.Forall₂ (TagOk baseContext) metadata.tags definedTags
  globalsValid : GlobalsOk baseContext metadata.globals definedGlobals
  memoriesValid : ∀ memory ∈ metadata.memories, MemOk memory
  tablesValid : List.Forall₂ (TableOk baseContext) metadata.tables definedTables
  funcs : Functions context definedFuncs
  dataValid : ∀ data ∈ metadata.data, DataOk context data
  elemsValid : List.Forall₂ (ElemOk context) metadata.elems elementTypes
  startValid : ∀ index, metadata.start = some index → StartOk context index
  exportsValid : List.Forall₂ (ExportOk context) metadata.exports interface.exports
  exportsDisjoint : (metadata.exports.map Export.name).Nodup

def Module.erase {interface} (module_ : Module interface) : Wasm.Module :=
  { module_.metadata with funcs := module_.funcs.erase }

end Silmaril.Wasm.Validation.Intrinsic
