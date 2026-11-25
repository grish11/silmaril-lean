module

public import SqliteWasm.WholeModule
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval
import Silmaril.Wasm.Auto2.Kernel.Thms

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Verify.Kernel (writeL writeL_eq)

set_option maxRecDepth 32768
set_option maxHeartbeats 600000

def reactorElementSegment : Elem := (sqlite.elems[0]?).get rfl

theorem reactorElementSegments : sqlite.elems = [reactorElementSegment] := rfl

theorem reactorElementSegmentMode :
    reactorElementSegment.mode = .active ⟨0⟩ [.intConst .i32 1] := rfl

theorem reactorElementSegmentLength : reactorElementSegment.init.length = 342 := rfl

theorem reactorTableMinimum :
    sqlite.tables.map (fun t => (t.type.address, t.type.limits.min.val)) = [(.i32, 343)] := rfl

/-- The ordinary Core initializer applies the reactor's active element segment with the
resolved table and segment entries. It writes the selected references and drops the segment. -/
theorem reactorElementSegmentApplied {H : Type} {s : Store H} {f : Frame}
    {tableAddr elemAddr : Nat} {table : TableInst} {elem : ElemInst}
    (mappedTable : s.table? f ⟨0⟩ = some (tableAddr, table))
    (mappedElem : s.elem? f ⟨0⟩ = some (elemAddr, elem))
    (destBound : 343 ≤ table.refs.length) (sourceSize : elem.refs.length = 342) :
    initElemSeg? evalConst? s f 0 reactorElementSegment =
      some ((s.setTable tableAddr
        { table with refs := table.refs.take 1 ++ elem.refs ++ table.refs.drop 343 }).setElem elemAddr []) := by
  have sourceBound : (0#32).toNat + 342 ≤ elem.refs.length := by
    change 342 ≤ elem.refs.length
    omega
  have tableRun := Silmaril.Proofs.Wasm.Auto2.Kernel.tableInitLoop_fast
    (a := .i32) (x := ⟨0⟩) (y := ⟨0⟩) 342 s table 1 0 342 rfl
    mappedTable mappedElem destBound sourceBound (by decide) (by decide)
  change tableInitLoop s f ⟨0⟩ ⟨0⟩ .i32 1 0 342 =
    some (s.setTable tableAddr { table with refs := writeL table.refs 1 (elem.refs.take 342) }) at tableRun
  have taking : elem.refs.take 342 = elem.refs := by
    rw [← sourceSize, List.take_length]
  rw [taking] at tableRun
  rw [writeL_eq _ _ _ (by omega), sourceSize] at tableRun
  unfold initElemSeg?
  rw [reactorElementSegmentMode, reactorElementSegmentLength]
  change (match tableInitLoop s f ⟨0⟩ ⟨0⟩ .i32 1 0 342 with
    | none => none
    | some next => elemDrop? next f ⟨0⟩) = _
  rw [tableRun]
  let updated := s.setTable tableAddr
    { table with refs := table.refs.take 1 ++ elem.refs ++ table.refs.drop 343 }
  change (s.elem? f ⟨0⟩).map (fun (address, _) => updated.setElem address []) = _
  rw [mappedElem]
  rfl

/-- Applying the complete element phase of the pinned reactor leaves the frame intact. -/
theorem reactorElementPhase {H : Type} {s : Store H} {f : Frame}
    {tableAddr elemAddr : Nat} {table : TableInst} {elem : ElemInst}
    (mappedTable : s.table? f ⟨0⟩ = some (tableAddr, table))
    (mappedElem : s.elem? f ⟨0⟩ = some (elemAddr, elem))
    (destBound : 343 ≤ table.refs.length) (sourceSize : elem.refs.length = 342) :
    initElem? evalConst? s f sqlite =
      some (((s.setTable tableAddr
        { table with refs := table.refs.take 1 ++ elem.refs ++ table.refs.drop 343 }).setElem elemAddr []), f) := by
  unfold initElem?
  rw [reactorElementSegments]
  change (match initElemSeg? evalConst? s f 0 reactorElementSegment with
    | none => none
    | some next => some next).map (·, f) = _
  rw [reactorElementSegmentApplied mappedTable mappedElem destBound sourceSize]
  rfl


end SqliteWasm
