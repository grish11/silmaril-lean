module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Defs

/-! Perform one original Φ's constant materialization before the add rules. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize

open Pure.SubZero (model word wordPort)
open RVSDG (Origin Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}

/-- The caller supplies the first binding in source scope order. -/
def select (g : AddPhi.Pair.Source inputs sigs) (first : Column) : Option (Column × BitVec 64) :=
  let columns := constantColumns g
  match columns first with
  | some value => some (first, value)
  | none => (columns first.other).map fun value => (first.other, value)

/-- Keep the other column's exact operand and all its producer scope. -/
def keepOther (column : Column) (arm : Arms.Arm Pure.SubZero.Opcode args past [word, word]) :
    Arms.Arm Pure.SubZero.Opcode args past [word] where
  sigs := arm.sigs
  dataflow := arm.dataflow
  outputs := .cons (arm.outputs.get column.other.port) .nil

/-- Put one literal in the chosen operand position. The two add
bindings keep their order, including when the literal is zero. -/
def suffix (column : Column) (value : BitVec 64) : Pure.Program Pure.SubZero.Opcode [word, word] word :=
  let inner : Origin (dataPorts [word, word]) [[wordPort]] wordPort := match column with
    | .left => .output (0 : Fin 1) .head
    | .right => .arg (.tail .head)
  let outer : Origin (dataPorts [word, word]) [[wordPort], [wordPort]] wordPort := match column with
    | .left => .arg (.tail .head)
    | .right => .output (0 : Fin 2) .head
  { dataflow := .cons (.literal value) .nil
      (.cons .add (.cons (.arg .head) (.cons inner .nil))
        (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons outer .nil)) .nil))
    result := .output (2 : Fin 3) .head }

def emit (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) (column : Column)
    (value : BitVec 64) : Program inputs sigs [word] where
  residual := x
  diamond := {
    shared := g.shared
    predicate := g.predicate
    merge := g.merge
    arms := fun slot => keepOther column (g.arms slot) }
  suffix := suffix column value

inductive Result (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) where
  | materialized (column : Column) (value : BitVec 64) (program : Program inputs sigs [word])
  | rotated (result : Dispatch.Result inputs sigs)

def Result.denote (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    BitVec 64 :=
  match result with
  | .materialized _ _ p => p.denote entry
  | .rotated result => result.denote entry

def Result.Returns (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (value : BitVec 64) : Prop :=
  match result with
  | .materialized _ _ p => p.Returns entry value
  | .rotated result => result.Returns entry value

/-- Emit exactly one original-column materialization when available.
Otherwise call the checked rotated dispatcher on the original nomination. -/
def rewrite (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) (first : Column) :
    Except Dispatch.Refusal (Result inputs sigs) :=
  match select g first with
  | some (column, value) => .ok (.materialized column value (emit g x column value))
  | none => (Dispatch.rewrite g x).map .rotated

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize
