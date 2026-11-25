module

public import SqliteWasm.WholeModule
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

set_option maxRecDepth 65536
set_option maxHeartbeats 600000

def reactorAllocationMemoryType : MemoryType := (sqlite.memories[0]?).get rfl

def reactorAllocationMemory : MemInst :=
  ⟨reactorAllocationMemoryType, ⟨Array.replicate 131072 0⟩⟩

def reactorAllocationData0 : DataInst := ⟨((sqlite.data[0]?).get rfl).bytes⟩
def reactorAllocationData1 : DataInst := ⟨((sqlite.data[1]?).get rfl).bytes⟩

/-- Successful allocation exposes the zeroed reactor memory and both original data entries. -/
theorem reactorAllocatedMemoryAndData {H : Type} {s after : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref}
    {elements : List (List Ref)}
    (alloc : allocModule? s sqlite imports globals tables elements = some (after, mi))
    (noMemoryImports : ExternAddr.mems imports = []) :
    after.mem? { module := mi } ⟨0⟩ = some (s.mems.length, reactorAllocationMemory) ∧
    after.data? { module := mi } ⟨0⟩ = some (s.datas.length, reactorAllocationData0) ∧
    after.data? { module := mi } ⟨1⟩ = some (s.datas.length + 1, reactorAllocationData1) := by
  obtain ⟨_, _, _, _, _, _, instanceShape, storeShape⟩ := allocModule?_inv alloc
  have memorySlots : mi.mems = [s.mems.length] := by
    rw [instanceShape]
    change ExternAddr.mems imports ++ List.range' s.mems.length 1 = _
    rw [noMemoryImports]
    rfl
  have memoryStore : after.mems = s.mems ++ [reactorAllocationMemory] := by
    rw [storeShape]
    rfl
  have dataSlots : mi.datas = [s.datas.length, s.datas.length + 1] := by
    rw [instanceShape]
    rfl
  have dataStore : after.datas = s.datas ++ [reactorAllocationData0, reactorAllocationData1] := by
    rw [storeShape]
    rfl
  constructor
  · change (mi.mems[0]?.bind fun a => after.mems[a]?.bind fun m => some (a, m)) = _
    rw [memorySlots, memoryStore]
    change (s.mems ++ [reactorAllocationMemory])[s.mems.length]?.bind (fun m => some (s.mems.length, m)) = _
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · constructor
    · change (mi.datas[0]?.bind fun a => after.datas[a]?.bind fun d => some (a, d)) = _
      rw [dataSlots, dataStore]
      change (s.datas ++ [reactorAllocationData0, reactorAllocationData1])[s.datas.length]?.bind
        (fun d => some (s.datas.length, d)) = _
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    · change (mi.datas[1]?.bind fun a => after.datas[a]?.bind fun d => some (a, d)) = _
      rw [dataSlots, dataStore]
      change (s.datas ++ [reactorAllocationData0, reactorAllocationData1])[s.datas.length + 1]?.bind
        (fun d => some (s.datas.length + 1, d)) = _
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      rfl

private def memoryTable : Table := (sqlite.tables[0]?).get rfl
private def activeElement : Elem := (sqlite.elems[0]?).get rfl

private def allocatedTable : TableInst :=
  ⟨⟨memoryTable.type.address, memoryTable.type.limits,
    (Validation.liftRef memoryTable.type.element).substAll ((allocTypes sqlite.types).map .dt)⟩,
    List.replicate 343 .null⟩

private def allocatedElement (refs : List Ref) : ElemInst :=
  ⟨(Validation.liftRef activeElement.type).substAll ((allocTypes sqlite.types).map .dt), refs⟩

/-- Given the supplied initializer values, successful allocation exposes the reactor's table,
element references and global 1. The source store may have pre-existing entries. -/
theorem reactorAllocatedTableElementAndGlobal {H : Type} {s after : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {refs : List Ref}
    (alloc : allocModule? s sqlite imports [.i32 126112, .i32 0] [.null] [refs] = some (after, mi))
    (noTableImports : ExternAddr.tables imports = [])
    (noGlobalImports : ExternAddr.globals imports = []) :
    (∃ table elem, after.table? { module := mi } ⟨0⟩ = some (s.tables.length, table) ∧
      table.refs = List.replicate 343 .null ∧
      after.elem? { module := mi } ⟨0⟩ = some (s.elems.length, elem) ∧ elem.refs = refs) ∧
    after.global? { module := mi } ⟨1⟩ = some (s.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) := by
  obtain ⟨_, _, _, _, _, _, instanceShape, storeShape⟩ := allocModule?_inv alloc
  have tableSlots : mi.tables = [s.tables.length] := by
    rw [instanceShape]
    change ExternAddr.tables imports ++ List.range' s.tables.length 1 = _
    rw [noTableImports]
    rfl
  have tableStore : after.tables = s.tables ++ [allocatedTable] := by
    rw [storeShape]
    rfl
  have elemSlots : mi.elems = [s.elems.length] := by
    rw [instanceShape]
    rfl
  have elemStore : after.elems = s.elems ++ [allocatedElement refs] := by
    rw [storeShape]
    rfl
  have globalSlots : mi.globals = [s.globals.length, s.globals.length + 1] := by
    rw [instanceShape]
    change ExternAddr.globals imports ++ List.range' s.globals.length 2 = _
    rw [noGlobalImports]
    rfl
  have globalStore : after.globals = s.globals ++
      [⟨⟨.var, .i32⟩, .i32 126112⟩, ⟨⟨.const, .i32⟩, .i32 0⟩] := by
    rw [storeShape]
    rfl
  refine ⟨⟨allocatedTable, allocatedElement refs, ?_, rfl, ?_, rfl⟩, ?_⟩
  · change (mi.tables[0]?.bind fun a => after.tables[a]?.bind fun t => some (a, t)) = _
    rw [tableSlots, tableStore]
    change (s.tables ++ [allocatedTable])[s.tables.length]?.bind
      (fun t => some (s.tables.length, t)) = _
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · change (mi.elems[0]?.bind fun a => after.elems[a]?.bind fun e => some (a, e)) = _
    rw [elemSlots, elemStore]
    change (s.elems ++ [allocatedElement refs])[s.elems.length]?.bind
      (fun e => some (s.elems.length, e)) = _
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · change (mi.globals[1]?.bind fun a => after.globals[a]?.bind fun g => some (a, g)) = _
    rw [globalSlots, globalStore]
    change (s.globals ++ [⟨⟨.var, .i32⟩, .i32 126112⟩, ⟨⟨.const, .i32⟩, .i32 0⟩])[s.globals.length + 1]?.bind (fun g => some (s.globals.length + 1, g)) = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rfl

#print axioms reactorAllocatedMemoryAndData
#print axioms reactorAllocatedTableElementAndGlobal

end SqliteWasm
