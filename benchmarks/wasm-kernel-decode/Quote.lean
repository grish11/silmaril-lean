module

public import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Thms
public meta import Lean.Elab.Deriving.ToExpr
public meta import Lean.Util.Recognizers
public meta import Lean.Elab.Tactic.Basic
public meta import Silmaril.Wasm.Perf.CoreDecode.Defs

public section

namespace WasmKernelBench

theorem reference_agrees (bytes : ByteArray) (result : Option Silmaril.Wasm.Module)
    (checked : Silmaril.Wasm.Perf.CoreDecode.decodeF bytes = result) :
    Silmaril.Wasm.Binary.Core.decode? bytes = result :=
  Silmaril.Wasm.Perf.CoreDecode.decodeF_eq ▸ checked

end WasmKernelBench

end

public meta section

namespace WasmKernelBench

open Lean Elab Command Silmaril Silmaril.Wasm

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

/-- Build separate source and module terms. This command asserts no agreement theorem. -/
elab "wasm_bench_defs " source:ident contents:ident " from " file:str : command => do
  let ns ← getCurrNamespace
  liftCoreM do
    let start ← IO.monoNanosNow
    let bytes ← KBytes.Elab.readRelative file.getString
    let readEnd ← IO.monoNanosNow
    let .ok decoded := Perf.CoreDecode.decodeModule bytes
      | throwError "wasm_bench_defs: Core decoder rejected {file.getString}"
    let parseEnd ← IO.monoNanosNow
    let value := toExpr decoded
    let quoteEnd ← IO.monoNanosNow
    let chunk := KBytes.Elab.chunkSize
    KBytes.Elab.defineKBytes (ns ++ source.getId) chunk bytes.size
      (KBytes.Elab.chunksOf bytes chunk) false
    let sourceEnd ← IO.monoNanosNow
    KBytes.Elab.addDefn (ns ++ contents.getId) (mkConst ``Wasm.Module) value false
    let moduleEnd ← IO.monoNanosNow
    logInfo m!"phases_ns read={readEnd - start} decode={parseEnd - readEnd} quote={quoteEnd - parseEnd} source={sourceEnd - quoteEnd} module={moduleEnd - sourceEnd}"

/-- Send a reflexivity proof directly to the kernel, avoiding a second reduction in a tactic. -/
elab "wasm_bench_agreement " name:ident reader:ident source:ident contents:ident : command => do
  let ns ← getCurrNamespace
  liftCoreM do
    let readerName ← realizeGlobalConstNoOverloadWithInfo reader
    let sourceName ← realizeGlobalConstNoOverloadWithInfo source
    let contentsName ← realizeGlobalConstNoOverloadWithInfo contents
    let target := mkApp (mkConst ``KBytes.toByteArray) (mkConst sourceName)
    let optionModule := mkApp (mkConst ``Option [0]) (mkConst ``Wasm.Module)
    let someModule := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Wasm.Module)
      (mkConst contentsName)
    let statement := KBytes.Elab.eqExpr optionModule (mkApp (mkConst readerName) target) someModule
    let proof := mkApp2 (mkConst ``Eq.refl [1]) optionModule someModule
    let start ← IO.monoNanosNow
    KBytes.Elab.addThm (ns ++ name.getId) statement proof
    let finish ← IO.monoNanosNow
    logInfo m!"agreement_ns {finish - start}"

/-- Check a closed equality directly in the kernel. The declaration type is elaborated first. -/
elab "wasm_bench_refl " name:ident " : " statement:term : command => do
  let type ← liftTermElabM do
    let type ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars type
  let some (_, _, rhs) := type.eq? | throwError "wasm_bench_refl expects an equality"
  let ns ← getCurrNamespace
  liftCoreM do
    let proof ← Meta.MetaM.run' (Meta.mkEqRefl rhs)
    let start ← IO.monoNanosNow
    KBytes.Elab.addThm (ns ++ name.getId) type proof
    let finish ← IO.monoNanosNow
    logInfo m!"agreement_ns {finish - start}"

/-- For explicit `decode? bytes = result` goals: send `decodeF` reflexivity and its transfer
to the kernel without running the elaborator's unifier over the decoding first. -/
elab "wasm_check_source" : tactic => do
  let goal ← Tactic.getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (type, lhs, rhs) := target.eq? | throwError "expected a `decode?` equality"
  unless lhs.isAppOfArity ``Wasm.Binary.Core.decode? 1 do
    throwError "expected an application of Core.decode? on the left"
  let refl := mkApp2 (mkConst ``Eq.refl [1]) type rhs
  goal.assign (mkApp3 (mkConst ``reference_agrees) lhs.appArg! rhs refl)
  Tactic.replaceMainGoal []

end WasmKernelBench
