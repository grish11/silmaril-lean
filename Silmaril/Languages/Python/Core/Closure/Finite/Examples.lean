module

import Silmaril.Languages.Python.Core.Closure.Finite.Thms
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Mathlib.Data.List.AList

/-! # Finite readback for Python closure store operations -/

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite

private abbrev sample : Layout := ⟨1, 1, 2⟩
private def allocated : CellId := ⟨0⟩
private def captured : Fin sample.captures → CellId := fun _ => allocated
private def initial : Snapshot sample :=
  ⟨HeapTable.empty.reserve 1, ⟨fun _ => none, fun _ => allocated, captured⟩⟩

private def fresh : Request sample := .fresh captured
private def write : Request sample := .write (.capture 0) (.int 37)
private def read : Request sample := .read (.capture 1)
private def readOwned : Request sample := .read (.owned 0)

private def newFrame := (execute initial.project fresh).2
private def newValue := (execute newFrame write).2

private theorem runtimeRun : (semantic sample).Execution initial.project
    [(fresh, .fresh), (write, .write (.ok ())), (read, .read (.ok (.int 37))),
      (readOwned, .read (.error (.defined (.unboundOwned 0))))]
    newValue [initial.project, newFrame, newValue, newValue, newValue] :=
  .stepL rfl (.stepL rfl (.stepL rfl (.stepL rfl (.refl _))))

example : ∃ final states, (presented sample).Execution initial
    [(fresh, .fresh), (write, .write (.ok ())), (read, .read (.ok (.int 37))),
      (readOwned, .read (.error (.defined (.unboundOwned 0))))]
    final states ∧
    states.map Snapshot.project = [initial.project, newFrame, newValue, newValue, newValue] ∧
    final.project = newValue :=
  execution_readback runtimeRun

example : newFrame.2.owned 0 = ⟨1⟩ ∧ newFrame.2.captures 0 = allocated ∧
    newFrame.2.captures 1 = allocated := ⟨rfl, rfl, rfl⟩

#guard
  let afterFresh := (initial.execute fresh).2
  let afterWrite := (afterFresh.execute write).2
  match (afterWrite.execute read).1, afterWrite.heap.rows.lookup 0,
    afterWrite.heap.project.lookup ⟨1⟩, afterWrite.heap.project.lookup ⟨2⟩ with
  | .read (.ok (.int 37)), some (.int 37), some none, none =>
    afterWrite.heap.next == 2 && (afterWrite.frame.owned 0).address == 1
  | _, _, _, _ => false

private def dangling : Snapshot sample := { initial with heap := HeapTable.empty }

example : dangling.execute read = (.read (.error (.danglingCell allocated)), dangling) := rfl

example : dangling.execute write = (.write (.error (.danglingCell allocated)), dangling) := rfl
