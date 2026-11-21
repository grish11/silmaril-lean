module

public import Silmaril.Wasm.ModuleParts.Defs
public import Silmaril.Wasm.Validation.Modules

@[expose] public section

namespace Silmaril.Wasm.Validation

/-- The Core `REFS` list, computed from the relevant sections instead of
manufacturing an empty function list. In particular, function exports and
element initializers still refer into the full function index space. -/
def sectionFuncRefs (secs : ModuleSections) : List Nat :=
  secs.globals.flatMap (fun global => Expr.freeFuncs global.init) ++
  secs.tables.flatMap (fun table => Expr.freeFuncs table.init) ++
  secs.elems.flatMap (fun elem => elem.init.flatMap Expr.freeFuncs ++ match elem.mode with
    | .active _ offset => Expr.freeFuncs offset
    | _ => []) ++
  secs.exports.flatMap (fun export_ => match export_.index with
    | .func index => [index.toNat]
    | _ => [])

def sectionBaseContext (secs : ModuleSections) (types : List DefType) (imports : List CExternType)
    (signatures : List DefType) : Context :=
  { types := types, globals := CExternType.globals imports
    funcs := CExternType.funcs imports ++ signatures, refs := sectionFuncRefs secs }

def sectionContext (secs : ModuleSections) (base : Context) (imports : List CExternType)
    (tags : List DefType) (globals : List CGlobalType) (tables : List CTableType) (elems : List CRefType) : Context :=
  { base with
    tags := CExternType.tags imports ++ tags, globals := base.globals ++ globals,
    mems := CExternType.mems imports ++ secs.memories, tables := CExternType.tables imports ++ tables,
    datas := secs.data.map fun _ => (), elems := elems }

end Silmaril.Wasm.Validation
