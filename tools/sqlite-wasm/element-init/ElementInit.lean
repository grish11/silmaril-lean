module

public import SqliteWasm.WholeModule
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Game.Instance.Defs

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

set_option maxRecDepth 32768
set_option maxHeartbeats 700000

def reactorElemIndices : List FuncIdx :=
  (((sqlite.elems[0]?).get rfl).init : List Expr).filterMap fun expression =>
    match expression with
    | [Instr.refFunc index] => some index
    | _ => none

def reactorElementRefs : List Ref := reactorElemIndices.map fun index => .func index.toNat

private theorem exactElementExpressions :
    sqlite.elems.map Elem.init = [reactorElemIndices.map fun index => [.refFunc index]] := rfl

private theorem reactorElemIndicesBounded :
    reactorElemIndices.all (fun index => decide (index.toNat < 1556)) = true := by decide +kernel

theorem reactorElementRefsLength : reactorElementRefs.length = 342 := rfl

private theorem evaluateRef {H : Type} {s : Store H} {f : Frame} {index : FuncIdx} {a : Nat}
    (slot : f.module.funcs[index.toNat]? = some a) :
    evalConst? s f [.refFunc index] = some (s, .ref (.func a)) := by
  simp [evalConst?, constExpr?, constInstr?, slot]

private theorem evaluateRefs {H : Type} {s : Store H} {f : Frame} {indices : List FuncIdx}
    (slots : ∀ index ∈ indices, f.module.funcs[index.toNat]? = some index.toNat) :
    evalExprs? evalConst? s f (indices.map fun index => [.refFunc index]) =
      some (s, f, indices.map fun index => .func index.toNat) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    have first := evaluateRef (s := s) (slots index List.mem_cons_self)
    have tail := ih fun i hi => slots i (List.mem_cons_of_mem _ hi)
    simp only [List.map_cons, evalExprs?, first, tail]

/-- The original reactor's single element initializer list evaluates to all 342 function
addresses in order in the ordinary Core evaluator, for a provisional frame with the
canonical address vector. This evaluator does not touch the incoming store. -/
theorem reactorElementReplay {H : Type} (s : Store H) (f : Frame)
    (addresses : f.module.funcs = List.range 1556) :
    evalExprss? evalConst? s f (sqlite.elems.map Elem.init) = some (s, f, [reactorElementRefs]) := by
  have slots : ∀ index ∈ reactorElemIndices, f.module.funcs[index.toNat]? = some index.toNat := by
    intro index present
    rw [addresses]
    exact List.getElem?_range (of_decide_eq_true (List.all_eq_true.mp reactorElemIndicesBounded _ present))
  rw [exactElementExpressions]
  simp only [evalExprss?, evaluateRefs (s := s) slots]
  rfl

def reactorTypedImports : Store Nat :=
  Silmaril.Wasm.Game.importStore
    ((sqlite.importedFunctions.mapM fun i => (allocTypes sqlite.types)[i.toNat]?).get rfl)

def reactorImportAddrs : List ExternAddr := (List.range 23).map ExternAddr.func

def reactorGlobalEvaluation :=
  evalGlobals? evalConst? reactorTypedImports
    ⟨[], ModuleInst.initial reactorTypedImports sqlite reactorImportAddrs⟩
    (Module.closedGlobalTypes sqlite) (sqlite.globals.map Global.init)

private def globalResult : Store Nat × Frame × List Val := reactorGlobalEvaluation.get rfl

private def tableEvaluation :=
  evalExprs? evalConst? globalResult.1 globalResult.2.1 (sqlite.tables.map Table.init)

private def tableResult : Store Nat × Frame × List Ref := tableEvaluation.get rfl

/-- On the provisional frame computed by the ordinary global and table evaluators for the
typed imports, a third ordinary evaluator call computes the exact element references. -/
theorem reactorProvisionalElementReplay :
    (do
      let (s, f, _) ← reactorGlobalEvaluation
      let (s', f', _) ← evalExprs? evalConst? s f (sqlite.tables.map Table.init)
      let (_, _, refs) ← evalExprss? evalConst? s' f' (sqlite.elems.map Elem.init)
      pure refs) = some [reactorElementRefs] := by
  have gh : reactorGlobalEvaluation = some globalResult := rfl
  have th : tableEvaluation = some tableResult := rfl
  have tableFrame : tableResult.2.1 = globalResult.2.1 :=
    (evalExprs?_shape (f' := tableResult.2.1) th).2.2
  have globalFuncs : globalResult.2.1.module.funcs =
      (ModuleInst.initial reactorTypedImports sqlite reactorImportAddrs).funcs := rfl
  have addressShape : tableResult.2.1.module.funcs = List.range 1556 := by
    rw [tableFrame, globalFuncs]
    change (List.range 23) ++ (List.range 1533).map (23 + ·) = List.range 1556
    rw [List.range_eq_range', List.range_eq_range', List.range_eq_range', List.map_add_range']
    exact List.range'_append_1
  change (reactorGlobalEvaluation.bind fun (s, f, _) =>
      (evalExprs? evalConst? s f (sqlite.tables.map Table.init)).bind fun (s', f', _) =>
      (evalExprss? evalConst? s' f' (sqlite.elems.map Elem.init)).bind fun (_, _, refs) =>
      some refs) = _
  rw [gh, Option.bind_some]
  change (tableEvaluation.bind fun (s', f', _) =>
      (evalExprss? evalConst? s' f' (sqlite.elems.map Elem.init)).bind fun (_, _, refs) =>
      some refs) = _
  rw [th, Option.bind_some]
  change (evalExprss? evalConst? tableResult.1 tableResult.2.1 (sqlite.elems.map Elem.init)).bind
    (fun (_, _, refs) => some refs) = _
  rw [reactorElementReplay _ _ addressShape]
  rfl


end SqliteWasm
