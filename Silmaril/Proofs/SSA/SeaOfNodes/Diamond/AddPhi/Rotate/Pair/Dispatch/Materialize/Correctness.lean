module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi (scanLiterals scanLiterals_agrees)
open AddPhi.Rotate (InputWord Program spine)
open AddPhi.Rotate.Pair.Dispatch (Column armWords constantColumns equalLiterals?)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Locals Port Tuple Wires extend)

private theorem read_get {args ports : List (Ty Unit)} {past : List (List (Ty Unit))}
    {t : Ty Unit} (port : Port ports t) (wires : Wires args past ports)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    (wires.read entry locals).get port = read model (wires.get port) entry locals := by
  induction port with
  | head =>
    cases wires
    rfl
  | tail port ih =>
    cases wires with
    | cons _ tail => exact ih tail

private theorem armWords_sound {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals args past} {arm : Arms.Arm Silmaril.SSA.SeaOfNodes.Pure.SubZero.Opcode args past [word, word]}
    {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
    {column : Column} {value : BitVec 64} (agree : Scan.Literals.Agrees known entry locals)
    (found : armWords known arm column = some value) :
    (arm.eval model entry locals).get column.port = value :=
  (read_get column.port arm.outputs entry _).trans
    (scanLiterals_agrees arm.dataflow known entry locals agree (arm.outputs.get column.port) found)

private theorem keepOther_eval {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (column : Column) (arm : Arms.Arm Silmaril.SSA.SeaOfNodes.Pure.SubZero.Opcode args past [word, word])
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    (keepOther column arm).eval model entry locals =
      .cons ((arm.eval model entry locals).get column.other.port) .nil :=
  congrArg (fun value : BitVec 64 => Tuple.cons (F := Val model.value) (t := wordPort) value .nil)
    (read_get column.other.port arm.outputs entry (arm.dataflow.eval model entry locals)).symm

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {first column : Column}
variable {value : BitVec 64} {result : Result inputs sigs}

theorem constantColumns_slot_eq (found : constantColumns g column = some value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    ((g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit)).get column.port = value := by
  let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
  have agrees : Scan.Literals.Agrees known entry (g.shared.eval model entry PUnit.unit) :=
    scanLiterals_agrees g.shared (fun _ => none) entry PUnit.unit (by intro _ _ _ h; contradiction)
  change equalLiterals? (armWords known (g.arms .first) column)
    (armWords known (g.arms .second) column) = some value at found
  unfold equalLiterals? at found
  obtain ⟨a, readFirst, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨b, readSecond, found⟩ := Option.bind_eq_some_iff.mp found
  split at found
  · rename_i same
    have firstValue := Option.some.inj found
    cases slot
    · exact (armWords_sound agrees readFirst).trans firstValue
    · exact (armWords_sound agrees readSecond).trans (same.symm.trans firstValue)
  · contradiction

theorem select_eq_some_iff :
    select g first = some (column, value) ↔
      (column = first ∧ constantColumns g column = some value) ∨
      (column = first.other ∧ constantColumns g first = none ∧ constantColumns g column = some value) := by
  cases found : constantColumns g first <;> cases first <;> cases column <;>
    simp [select, found, Column.other]

private theorem suffix_eval (column : Column) (value capture : BitVec 64) (row : AddPhi.Pair.Operands)
    (same : row.get column.port = value) :
    (suffix column value).eval model (.cons capture (.cons (row.get column.other.port) .nil)) =
      spine.eval model (.cons capture row) := by
  cases row with
  | cons left tail =>
    cases tail with
    | cons right tail =>
      cases tail
      cases column
      · change left = value at same
        subst value
        rfl
      · change right = value at same
        subst value
        rfl

theorem emit_slot_eval_eq (found : constantColumns g column = some value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (emit g x column value).atSlot entry slot = (AddPhi.Rotate.Pair.original g x).atSlot entry slot := by
  let locals := g.shared.eval model entry PUnit.unit
  have kept := keepOther_eval column (g.arms slot) entry locals
  calc
    _ = (suffix column value).eval model
        (.cons (entry.get x) (.cons (((g.arms slot).eval model entry locals).get column.other.port) .nil)) :=
      congrArg (fun row => (suffix column value).eval model (.cons (entry.get x) row)) kept
    _ = _ := suffix_eval column value (entry.get x) ((g.arms slot).eval model entry locals)
      (constantColumns_slot_eq found entry slot)

private theorem emit_denote_eq (found : constantColumns g column = some value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (emit g x column value).denote entry = (AddPhi.Rotate.Pair.original g x).denote entry := by
  let slot := g.merge.slot (Projection.ofBool
    (read model g.predicate entry (g.shared.eval model entry PUnit.unit)).down)
  exact emit_slot_eval_eq found entry slot

theorem rewrite_eq_ok_iff :
    rewrite g x first = .ok result ↔
      (∃ column value, select g first = some (column, value) ∧
        result = .materialized column value (emit g x column value)) ∨
      (select g first = none ∧
        ∃ rotated, AddPhi.Rotate.Pair.Dispatch.rewrite g x = .ok rotated ∧ result = .rotated rotated) := by
  cases selected : select g first with
  | none =>
    cases dispatched : AddPhi.Rotate.Pair.Dispatch.rewrite g x <;>
      simp [rewrite, selected, dispatched, Except.map, eq_comm]
  | some hit =>
    obtain ⟨column, value⟩ := hit
    simp [rewrite, selected, eq_comm]

theorem rewrite_returns_iff (accepted : rewrite g x first = .ok result)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    result.Returns entry returned ↔ (AddPhi.Rotate.Pair.original g x).Returns entry returned := by
  rcases rewrite_eq_ok_iff.mp accepted with ⟨column, value, selected, rfl⟩ | ⟨_, rotated, found, rfl⟩
  · have known := (select_eq_some_iff.mp selected).elim And.right (fun second => second.2.2)
    change (emit g x column value).Returns entry returned ↔ _
    rw [Program.returns_iff_denote, Program.returns_iff_denote, emit_denote_eq known]
  · exact AddPhi.Rotate.Pair.Dispatch.rewrite_returns_iff found entry returned

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize
