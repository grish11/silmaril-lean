module

import Silmaril.Machine.SQLite.VirtualMachine.Concurrent.Thms

namespace Silmaril.Machine.SQLite.VirtualMachine.Concurrent

open Silmaril.Formats.Sqlite
open Silmaril.Semantics.TrackA

private def jobs (mutex : Bool) : Bool → Client
  | false => ⟨.query (pointProgram 0 2 0 42) 6 initial, .plain, mutex⟩
  | true => ⟨.publish 1, .plain, mutex⟩

private def versions (generation : Nat) : Database := fun database root =>
  if database = 0 ∧ root = 2 then
    some (BTree.Query.ReadModel.ofList [(42, [.integer (Int64.ofInt generation)])])
  else none

private def queryView (schedule : List Bool) : Option (List (QueryReport Bool)) := do
  let observation ← (simulate .mixed (jobs true) versions 0 schedule).join
  return observation.queries

example : queryView [false, false, false, true, true, true] =
    some [⟨false, 0, ⟨[.openRead 0 2 true, .row [.integer 0]], ⟨[[.integer 0]], .halted 0⟩⟩⟩] :=
  by decide

example : queryView [true, true, true, false, false, false] =
    some [⟨false, 1, ⟨[.openRead 0 2 true, .row [.integer 1]], ⟨[[.integer 1]], .halted 0⟩⟩⟩] :=
  by decide

example : simulate .mixed (jobs true) versions 0 [false, true] = none := by decide

example : simulate .mixed (jobs false) versions 0 [false, true] = some none := by decide

example : none ∈ explicit .mixed (jobs false) versions 0 :=
  simulate_ub_iff.mpr ⟨[false, true], by decide⟩

example : catastrophic .mixed (jobs false) versions 0 = ⊤ :=
  catastrophic_eq_top_iff.mpr (simulate_ub_iff.mpr ⟨[false, true], by decide⟩)

example :
    ((simulate .mixed (jobs false) (fun _ _ _ => none) 0 [false]).join.map Report.queries) =
      some [⟨false, 0, ⟨[.openRead 0 2 false], ⟨[], .fault (.missingTable 0 2)⟩⟩⟩] := by decide

end Silmaril.Machine.SQLite.VirtualMachine.Concurrent
