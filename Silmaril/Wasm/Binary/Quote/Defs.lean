module

public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public meta import Lean.Elab.Deriving.ToExpr
public meta import Lean.Elab.Term
public meta import Silmaril.Wasm.Binary.Core.Decode

/-! Quote a Core binary into an explicit module term. The compiled Core decoder runs during
elaboration, not in the generated term. Quotation claims neither source agreement nor validity. -/

public meta section

namespace Silmaril.Wasm.Binary.Quote

open Lean Elab Command Silmaril.Wasm
local instance {Left Right : Type} [ToExpr Left] [ToExpr Right] : ToExpr (Left × Right) where
  toTypeExpr := mkApp2 (mkConst ``Prod [0, 0]) (toTypeExpr Left) (toTypeExpr Right)
  toExpr pair := mkApp4 (mkConst ``Prod.mk [0, 0]) (toTypeExpr Left) (toTypeExpr Right)
    (toExpr pair.1) (toExpr pair.2)

local instance : ToExpr ByteArray where
  toTypeExpr := mkConst ``ByteArray
  toExpr bytes :=
    let chunk := KBytes.Elab.chunkSize
    let chunks := (KBytes.Elab.chunksOf bytes chunk).map mkNatLit
    let (tree, _) := KBytes.Elab.treeExpr chunk chunks 0 chunks.size bytes.size
    mkApp (mkConst ``KBytes.toByteArray) tree

deriving instance ToExpr for IndexKind

local instance {kind : IndexKind} : ToExpr (Idx kind) where
  toTypeExpr := mkApp (mkConst ``Idx) (toExpr kind)
  toExpr index := mkApp2 (mkConst ``Idx.mk) (toExpr kind) (toExpr index.value)
deriving instance ToExpr for IntType
deriving instance ToExpr for FloatType
deriving instance ToExpr for NumType
deriving instance ToExpr for VecType
deriving instance ToExpr for AddrType
deriving instance ToExpr for AbsHeapType
deriving instance ToExpr for HeapType
deriving instance ToExpr for RefType
deriving instance ToExpr for ValType
deriving instance ToExpr for PackType
deriving instance ToExpr for StorageType
deriving instance ToExpr for Mutability
deriving instance ToExpr for FieldType
deriving instance ToExpr for FuncType
deriving instance ToExpr for CompositeType
deriving instance ToExpr for SubType
deriving instance ToExpr for RecType
deriving instance ToExpr for BlockType
deriving instance ToExpr for Limits
deriving instance ToExpr for MemoryType
deriving instance ToExpr for TableType
deriving instance ToExpr for GlobalType
deriving instance ToExpr for ExternType
deriving instance ToExpr for Signedness
deriving instance ToExpr for PackSize
deriving instance ToExpr for IntUnOp
deriving instance ToExpr for IntBinOp
deriving instance ToExpr for IntTestOp
deriving instance ToExpr for IntRelOp
deriving instance ToExpr for FloatUnOp
deriving instance ToExpr for FloatBinOp
deriving instance ToExpr for FloatRelOp
deriving instance ToExpr for ConvertOp
deriving instance ToExpr for IntShape
deriving instance ToExpr for FloatShape
deriving instance ToExpr for Shape
deriving instance ToExpr for Half
deriving instance ToExpr for VecUnOp
deriving instance ToExpr for VecBinOp
deriving instance ToExpr for VecTernOp
deriving instance ToExpr for VecTestOp
deriving instance ToExpr for VecIntUnOp
deriving instance ToExpr for VecIntBinOp
deriving instance ToExpr for VecFloatBinOp
deriving instance ToExpr for VecIntTernOp
deriving instance ToExpr for VecFloatTernOp
deriving instance ToExpr for VecShiftOp
deriving instance ToExpr for VecSwizzleOp
deriving instance ToExpr for VecExtUnOp
deriving instance ToExpr for VecExtBinOp
deriving instance ToExpr for VecExtTernOp
deriving instance ToExpr for VecConvertOp
deriving instance ToExpr for VecLoadOp
deriving instance ToExpr for MemArg
deriving instance ToExpr for Catch
deriving instance ToExpr for Instr
deriving instance ToExpr for Declaration.Func
deriving instance ToExpr for Declaration.Global
deriving instance ToExpr for ExternIdx
deriving instance ToExpr for Wasm.Import
deriving instance ToExpr for Export
deriving instance ToExpr for Table
deriving instance ToExpr for ElemMode
deriving instance ToExpr for Elem
deriving instance ToExpr for DataMode
deriving instance ToExpr for Data
deriving instance ToExpr for Wasm.Module

/-- Quote the decoded value as constructors; only embedded byte arrays use packed literals. -/
def quoteModule (decoded : Wasm.Module) : Lean.Expr := toExpr decoded

private def readModule (file : TSyntax `str) : CoreM (ByteArray × Lean.Expr) := withRef file do
  let bytes ← KBytes.Elab.readRelative file.getString
  match Core.Decode.decodeModule bytes with
  | .ok decoded => return (bytes, quoteModule decoded)
  | .error msg => throwError "wasm_module: {msg}"

/-- `wasm_module% "file.wasm"` elaborates to an explicit `Wasm.Module`. The path is relative
 to the current Lean source file. -/
elab "wasm_module% " file:str : term => do
  let (_, quoted) ← readModule file
  return quoted

private def defineFile (contents : TSyntax `ident) (file : TSyntax `str)
    (source : Option (TSyntax `ident)) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  liftCoreM do
    let resultName := ns ++ contents.getId
    if let some source := source then
      if source.getId == contents.getId then
        throwErrorAt source "wasm_module: source and module names must differ"
    let (bytes, quoted) ← readModule file
    KBytes.Elab.addDefn resultName (mkConst ``Wasm.Module) quoted false
    if let some source := source then
      let chunk := KBytes.Elab.chunkSize
      KBytes.Elab.defineKBytes (ns ++ source.getId) chunk bytes.size
        (KBytes.Elab.chunksOf bytes chunk) false

/-- Publish an explicit Wasm module. The importing module does not read the file. -/
elab "wasm_module " contents:ident &" from " file:str : command =>
  defineFile contents file none

/-- Publish independent packed bytes alongside the explicit module. Import `Quote.Agreement`
to prove a source equation separately. -/
elab "wasm_module " contents:ident &" from " file:str &" with_source " source:ident : command =>
  defineFile contents file (some source)

end Silmaril.Wasm.Binary.Quote
