module

public import SqliteWasm.ElementInit
public import SqliteWasm.PreparationBounds
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

set_option maxRecDepth 65536
set_option maxHeartbeats 900000

private theorem mapM_exists {A B : Type} (read : A → Option B) (items : List A)
    (total : ∀ item ∈ items, ∃ value, read item = some value) :
    ∃ values, items.mapM read = some values := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := total x List.mem_cons_self
    obtain ⟨ys, hys⟩ := ih fun z hz => total z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

private def closedTypes := allocTypes sqlite.types

private theorem closedTypesBound :
    sqlite.funcs.all (fun f => decide (f.type.toNat < closedTypes.length)) = true := by decide +kernel

private theorem resolvedTypes :
    ∃ types, sqlite.funcs.mapM (fun f => closedTypes[f.type.toNat]?) = some types := by
  apply mapM_exists
  intro f member
  have bound := of_decide_eq_true (List.all_eq_true.mp closedTypesBound f member)
  exact ⟨closedTypes[f.type.toNat], List.getElem?_eq_getElem bound⟩

private def globalStage := reactorGlobalEvaluation.get rfl

private def evalTable :=
  evalExprs? evalConst? globalStage.1 globalStage.2.1 (sqlite.tables.map Table.init)

private def tableStage := evalTable.get rfl

private theorem canonicalAddresses :
    List.range 23 ++ (List.range 1533).map (23 + ·) = List.range 1556 := by
  rw [List.range_eq_range', List.range_eq_range', List.range_eq_range', List.map_add_range']
  exact List.range'_append_1

private theorem stageAddressShape : tableStage.2.1.module.funcs = List.range 1556 :=
  canonicalAddresses

private def exportView : ModuleInst :=
  { tags := ExternAddr.tags reactorImportAddrs ++ List.range' tableStage.1.tags.length 0,
    globals := ExternAddr.globals reactorImportAddrs ++
      List.range' tableStage.1.globals.length (min sqlite.globals.length globalStage.2.2.length),
    mems := ExternAddr.mems reactorImportAddrs ++ List.range' tableStage.1.mems.length sqlite.memories.length,
    tables := ExternAddr.tables reactorImportAddrs ++
      List.range' tableStage.1.tables.length (min sqlite.tables.length tableStage.2.2.length),
    funcs := ExternAddr.funcs reactorImportAddrs ++
      (List.range sqlite.funcs.length).map (tableStage.1.funcs.length + ·) }

private theorem exportViewAddresses : exportView.funcs = List.range 1556 :=
  canonicalAddresses

private def exportIndicesOk : Bool :=
  sqlite.exports.all fun e => match e.index with
    | .func index => decide (index.toNat < 1556)
    | .memory index => decide (index.toNat = 0)
    | _ => false

private theorem allExportsInRange : exportIndicesOk = true := by decide +kernel

private theorem exportListResolved :
    ∃ exports, sqlite.exports.mapM (allocExport? exportView) = some exports := by
  apply mapM_exists
  intro e present
  have ok := List.all_eq_true.mp allExportsInRange e present
  cases hx : e.index with
  | func index =>
    rw [hx] at ok
    have bound : index.toNat < 1556 := of_decide_eq_true ok
    refine ⟨⟨e.name, .func index.toNat⟩, ?_⟩
    unfold allocExport?
    rw [hx]
    change (exportView.funcs[index.toNat]?.map ExternAddr.func).map (ExportInst.mk e.name) = _
    rw [exportViewAddresses, List.getElem?_range bound]
    rfl
  | memory index =>
    rw [hx] at ok
    have zero : index.toNat = 0 := of_decide_eq_true ok
    refine ⟨⟨e.name, .mem 0⟩, ?_⟩
    unfold allocExport?
    rw [hx]
    change (exportView.mems[index.toNat]?.map ExternAddr.mem).map (ExportInst.mk e.name) = _
    rw [zero]
    rfl
  | tag index => simp [hx] at ok
  | global index => simp [hx] at ok
  | table index => simp [hx] at ok

private theorem projectedAllocation :
    (allocModule? tableStage.1 sqlite reactorImportAddrs
      globalStage.2.2 tableStage.2.2 [reactorElementRefs]).map
      (fun p => p.2.funcs[25]?) = some (some 25) := by
  obtain ⟨types, typesDone⟩ := resolvedTypes
  obtain ⟨exports, exportsDone⟩ := exportListResolved
  have tagsDone : sqlite.tags.mapM (fun x => closedTypes[x.toNat]?) = some [] := rfl
  unfold closedTypes at tagsDone typesDone
  unfold allocModule?
  simp only [Option.bind_eq_bind, tagsDone, typesDone, Option.bind_some,
    allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq, allocMany_table_eq,
    allocMany_data_eq, allocMany_elem_eq, List.length_zip, List.length_map, List.length_nil]
  unfold exportView at exportsDone
  rw [exportsDone, Option.bind_some]
  change some (exportView.funcs[25]?) = some (some 25)
  rw [exportViewAddresses, List.getElem?_range (by decide)]

private theorem prepareOfStages {H : Type} {m : Module} {initial sg st se : Store H}
    {fg ft fe : Frame} {imports : List ExternAddr} {globals : List Val}
    {tables : List Ref} {elems : List (List Ref)} {address : Nat}
    (bounded : m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32))
    (globalDone : evalGlobals? evalConst? initial ⟨[], ModuleInst.initial initial m imports⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (sg, fg, globals))
    (tableDone : evalExprs? evalConst? sg fg (m.tables.map Table.init) = some (st, ft, tables))
    (elemDone : evalExprss? evalConst? st ft (m.elems.map Elem.init) = some (se, fe, elems))
    (projection : (allocModule? se m imports globals tables elems).map (fun p => p.2.funcs[25]?) =
      some (some address)) :
    (prepare? evalConst? initial m imports).map (fun p => (p.1.frame.module.funcs[25]?, p.2)) =
      some (some address, m.start) := by
  unfold Module.closedGlobalTypes at globalDone
  unfold prepare?
  simp only [ite_eq_left bounded, globalDone, tableDone, elemDone]
  generalize state : allocModule? se m imports globals tables elems = result at projection ⊢
  cases result with
  | none => cases projection
  | some pair =>
    obtain ⟨store, mi⟩ := pair
    have slot : mi.funcs[25]? = some address := Option.some.inj projection
    change some (mi.funcs[25]?, m.start) = some (some address, m.start)
    rw [slot]

/-- The ordinary preparer succeeds for the pinned reactor and the canonical typed import store,
with runtime slot 25 at address 25 and no Start call. -/
theorem reactorPreparedInitializerSlot : (prepare? evalConst? reactorTypedImports sqlite reactorImportAddrs).map
    (fun p => (p.1.frame.module.funcs[25]?, p.2)) = some (some 25, none) := by
  have globalDone : reactorGlobalEvaluation = some (globalStage.1, globalStage.2.1, globalStage.2.2) := rfl
  have tableDone : evalTable = some (tableStage.1, tableStage.2.1, tableStage.2.2) := rfl
  exact prepareOfStages (m := sqlite) (initial := reactorTypedImports) (imports := reactorImportAddrs)
    reactorSegmentBounds globalDone tableDone
    (reactorElementReplay tableStage.1 tableStage.2.1 stageAddressShape) projectedAllocation

theorem reactorPrepared : ∃ c,
    prepare? evalConst? reactorTypedImports sqlite reactorImportAddrs = some (c, none) ∧
    c.frame.module.funcs[25]? = some 25 := by
  obtain ⟨result, prepared, projection⟩ := Option.map_eq_some_iff.mp reactorPreparedInitializerSlot
  obtain ⟨c, start⟩ := result
  obtain ⟨slot, noStart⟩ := Prod.mk.inj projection
  exact ⟨c, noStart ▸ prepared, slot⟩

end SqliteWasm
