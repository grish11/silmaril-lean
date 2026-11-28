module

import Silmaril.Semantics.Relational.Scan.Defs

/-! Small kernel-checked vectors for ordered projection and nullable filtering. -/

namespace Silmaril.Relational.Scan

private inductive Kind where
  | number
  | text

private def Value : Kind → Type
  | .number => Nat
  | .text => String

private def schema : Schema (Nat × String) Kind :=
  ⟨2, Fin.cases ((1, "field"), .number) (fun _ => ((2, "field"), .text))⟩

private def row (number : Option Nat) (text : Option String) : Row schema Value :=
  Fin.cases (motive := fun i => Option (Value (schema.kind i).2)) number (fun _ => text)

private def input : Table schema Value :=
  [row (some 4) (some ""), row none (some "unknown"), row (some 5) (some "false"),
    row (some 4) none, row (some 4) (some "")]

private def predicate : Predicate schema Value := fun r =>
  Option.map (fun number : Nat => number == 4) (r (0 : Fin 2))

private def reordered : Projection schema := Projection.ofArray (#[1, 0, 1] : Array (Fin 2))

example : List.ofFn (fun i => (reordered.schema.kind i).1.1) = [2, 1, 2] := rfl

example : (reordered.scan predicate input).map
    (fun r => (r (0 : Fin 3), r (1 : Fin 3), r (2 : Fin 3))) =
    ([(some "", some 4, some ""), (none, some 4, none), (some "", some 4, some "")] :
      List (Option String × Option Nat × Option String)) := rfl

private def emptyProjection : Projection schema := Projection.ofArray #[]

example : (emptyProjection.scan predicate input).length = 3 := rfl

example : (Observation.ofColumns emptyProjection.schema
    (emptyProjection.projectColumns (AlignedColumns.ofRows input))).rowCount = 5 := rfl

end Silmaril.Relational.Scan
