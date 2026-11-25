module

public import SqliteWasm.CorePreparation
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
import SqliteWasm.AllocatedSegments

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

set_option maxRecDepth 65536
set_option maxHeartbeats 700000

private theorem allocatedFromStages {H : Type} {m : Module} {initial sg st se : Store H}
    {fg ft fe : Frame} {imports : List ExternAddr} {globals : List Val}
    {tables : List Ref} {elems : List (List Ref)} {c : Config H} {start : Option FuncIdx}
    (bounded : m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32))
    (globalDone : evalGlobals? evalConst? initial ⟨[], ModuleInst.initial initial m imports⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (sg, fg, globals))
    (tableDone : evalExprs? evalConst? sg fg (m.tables.map Table.init) = some (st, ft, tables))
    (elemDone : evalExprss? evalConst? st ft (m.elems.map Elem.init) = some (se, fe, elems))
    (prepared : prepare? evalConst? initial m imports = some (c, start)) :
    allocModule? se m imports globals tables elems = some (c.store, c.frame.module) ∧
      c.frame = { module := c.frame.module } := by
  unfold Module.closedGlobalTypes at globalDone
  unfold prepare? at prepared
  simp only [ite_eq_left bounded, globalDone, tableDone, elemDone] at prepared
  split at prepared
  · cases prepared
  · rename_i allocated mi equation
    have config := (Prod.mk.inj (Option.some.inj prepared)).1
    rw [← config]
    exact ⟨equation, rfl⟩

private def globalStage := reactorGlobalEvaluation.get rfl

private def evalTable :=
  evalExprs? evalConst? globalStage.1 globalStage.2.1 (sqlite.tables.map Table.init)

private def tableStage := evalTable.get rfl

private theorem globalsDone :
    reactorGlobalEvaluation = some (globalStage.1, globalStage.2.1, [.i32 126112, .i32 0]) := rfl

private theorem tableDone : evalTable = some (tableStage.1, tableStage.2.1, [.null]) := rfl

private theorem elementStage : ∃ s f,
    evalExprss? evalConst? tableStage.1 tableStage.2.1 (sqlite.elems.map Elem.init) =
      some (s, f, [reactorElementRefs]) := by
  have replay := reactorProvisionalElementReplay
  change (reactorGlobalEvaluation.bind fun (s, f, _) =>
      (evalExprs? evalConst? s f (sqlite.tables.map Table.init)).bind fun (s', f', _) =>
        (evalExprss? evalConst? s' f' (sqlite.elems.map Elem.init)).bind
          (fun (_, _, refs) => some refs)) = some [reactorElementRefs] at replay
  rw [globalsDone, Option.bind_some] at replay
  change (evalTable.bind fun (s', f', _) =>
    (evalExprss? evalConst? s' f' (sqlite.elems.map Elem.init)).bind
      (fun (_, _, refs) => some refs)) = some [reactorElementRefs] at replay
  rw [tableDone, Option.bind_some] at replay
  have runs : (evalExprss? evalConst? tableStage.1 tableStage.2.1 (sqlite.elems.map Elem.init)).bind
      (fun (_, _, refs) => some refs) = some [reactorElementRefs] := replay
  obtain ⟨⟨s, f, refs⟩, evaluated, eq⟩ := Option.bind_eq_some_iff.mp runs
  have equal : refs = [reactorElementRefs] := Option.some.inj eq
  exact ⟨s, f, equal ▸ evaluated⟩

private theorem preparedAllocation :
    ∃ before c,
      prepare? evalConst? reactorTypedImports sqlite reactorImportAddrs = some (c, none) ∧
      c.frame.module.funcs[25]? = some 25 ∧
      c.frame = { module := c.frame.module } ∧
      allocModule? before sqlite reactorImportAddrs [.i32 126112, .i32 0]
        [.null] [reactorElementRefs] = some (c.store, c.frame.module) := by
  obtain ⟨c, prepared, slot⟩ := reactorPrepared
  obtain ⟨before, pf, elemDone⟩ := elementStage
  have ⟨alloc, frameShape⟩ :=
    allocatedFromStages reactorSegmentBounds globalsDone tableDone elemDone prepared
  exact ⟨before, c, prepared, slot, frameShape, alloc⟩

private theorem directOfPrepared {H : Type} {s runtime : Store H} {m : Module}
    {imports : List ExternAddr} {c : Config H} {start : Option FuncIdx}
    (prepared : prepare? evalConst? s m imports = some (c, start))
    (segments : initSegments? evalConst? c.store c.frame m = some (runtime, c.frame)) :
    prepareDirect? evalConst? s m imports = some (runtime, c.frame, start) := by
  unfold prepareDirect?
  simp only [prepared, segments]

/-- Ordinary direct preparation for the pinned reactor and its typed import fixture, including
segment application and the two startup memory words. -/
theorem reactorDirectPreparation :
    ∃ before allocated runtime frame mem,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      allocModule? before sqlite reactorImportAddrs [.i32 126112, .i32 0]
        [.null] [reactorElementRefs] = some (allocated, frame.module) ∧
      runtime.funcs = allocated.funcs ∧ frame.module.funcs[25]? = some 25 ∧
      runtime.global? frame ⟨1⟩ =
        some (before.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) ∧
      runtime.mem? frame ⟨0⟩ = some (before.mems.length, mem) ∧
      mem.bytes.size = 131072 ∧
      Memory.load mem.bytes 59328 4 = some 0 ∧ Memory.load mem.bytes 59892 4 = some 0 := by
  obtain ⟨before, c, prepared, entry, frameShape, alloc⟩ := preparedAllocation
  obtain ⟨runtime, mem, segments, functions, global, mapped, size, flag, word⟩ :=
    reactorAllocatedSegments alloc
  have segs : initSegments? evalConst? c.store c.frame sqlite = some (runtime, c.frame) := by
    rw [frameShape]
    exact segments
  have direct := directOfPrepared prepared segs
  have g : runtime.global? c.frame ⟨1⟩ =
      some (before.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) := by
    rw [frameShape]
    exact global
  have m : runtime.mem? c.frame ⟨0⟩ = some (before.mems.length, mem) := by
    rw [frameShape]
    exact mapped
  exact ⟨before, c.store, runtime, c.frame, mem, direct, alloc, functions, entry, g, m, size, flag, word⟩

#print axioms reactorDirectPreparation

end SqliteWasm
