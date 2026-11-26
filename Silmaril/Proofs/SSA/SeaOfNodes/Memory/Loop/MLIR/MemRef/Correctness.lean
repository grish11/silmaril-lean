module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.StraightLine.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Proofs

open RVSDG (Locals Origin Port Tuple Wires)
open RVSDG.MLIR.Graph.Feedback (Code Operands)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (olderIndex olderPort weaken)
open RVSDG.OrderedRuntime.Structured (Values newestIndex newestPort readOrigin read_cons)
open Silmaril.MLIR.MemRef (Buffer Ty Value wordPorts)
open SeaOfNodes.Memory.MLIR.MemRef (encodeInput encodeScalars encodeValue entryPorts scalarPort)

variable {cells : Nat} {args : List ValueSort}

private abbrev BlockValues (cells : Nat) := Values (Value cells)

private theorem read_older {extra : List (Ty cells)} {t : Ty cells} (result : Tuple (BlockValues cells) extra) :
    (scope : List (List (Ty cells))) → (i : Fin scope.length) → (port : Port scope[i] t) →
    (env : Locals (BlockValues cells) scope) →
    ((env.snoc result).get (olderIndex extra scope i)).get (olderPort extra scope i port) = (env.get i).get port
  | [], i => i.elim0
  | front :: tail, i =>
    Fin.cases (motive := fun j => ∀ (port : Port (front :: tail)[j] t)
      (env : Locals (BlockValues cells) (front :: tail)),
      ((env.snoc result).get (olderIndex extra (front :: tail) j)).get (olderPort extra (front :: tail) j port) =
        (env.get j).get port)
      (fun _ _ => rfl) (fun j port env => read_older result tail j port env.2) i

private theorem read_weaken {scope : List (List (Ty cells))} {extra : List (Ty cells)} {t : Ty cells}
    (wire : Origin [] scope t) (env : Locals (BlockValues cells) scope) (result : Tuple (BlockValues cells) extra) :
    readOrigin (weaken extra wire) .nil (env.snoc result) = readOrigin wire .nil env := by
  cases wire with
  | arg port => cases port
  | output i port => exact read_older result scope i port env

private theorem read_newest {scope : List (List (Ty cells))} {extra : List (Ty cells)} {t : Ty cells}
    (port : Port extra t) (env : Locals (BlockValues cells) scope) (result : Tuple (BlockValues cells) extra) :
    readOrigin (.output (newestIndex extra scope) (newestPort port scope)) .nil (env.snoc result) =
      result.get port := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact ih env.2

private def after (graph : Graph args) (values : Tuple (BlockValues cells) (wordPorts cells))
    (entry : Tuple (BlockValues cells) (entryPorts cells args)) :
    StateM (Buffer cells) (Tuple (BlockValues cells) (activationPorts cells)) :=
  pure (.cons (tailSelector (values.get .head) (entry.get (.tail (scalarPort graph.stop)))) values)

private theorem tail_eval (graph : Graph args) {past : List (List (Ty cells))}
    (wires : Operands (entryPorts cells args :: past) (wordPorts cells))
    (env : Locals (BlockValues cells) (entryPorts cells args :: past)) :
    (tailCode graph wires).val.runStraightLine (runOp cells) (tailCode graph wires).property env =
      after graph (wires.read .nil env) env.1 := by
  cases wires with
  | cons word rest =>
    cases rest
    funext initial
    simp only [tailCode, Tuple.get, Code.runStraightLine]
    erw [read_cons word (.cons (stopWire graph past) .nil) .nil env,
      read_cons (stopWire graph past) .nil .nil env]
    let test := tailSelector (readOrigin word .nil env) (readOrigin (stopWire graph past) .nil env)
    let result : Tuple (BlockValues cells) (testPorts cells) := .cons test .nil
    let scope := entryPorts cells args :: past
    let selector := Origin.output (args := []) (newestIndex (testPorts cells) scope) (newestPort .head scope)
    change (Wires.read (.cons selector (.cons (weaken (testPorts cells) word) .nil)) .nil (env.snoc result),
      initial) = _
    erw [read_cons selector (.cons (weaken (testPorts cells) word) .nil) .nil (env.snoc result),
      read_cons (weaken (testPorts cells) word) .nil .nil (env.snoc result),
      read_cons word .nil .nil env, read_newest .head env result, read_weaken word env result]
    rfl

private theorem body_run (graph : Memory.Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Silmaril.MLIR.MemRef.run (SeaOfNodes.Memory.MLIR.MemRef.lower cells graph)
        (encodeInput input, PUnit.unit) initial =
      let result := graph.denote input initial.cell
      ((.cons result.1 .nil : Tuple (BlockValues cells) (wordPorts cells)), Buffer.mk result.2) := by
  have observed := SeaOfNodes.Memory.MLIR.MemRef.lower_run graph input initial
  unfold SeaOfNodes.Memory.MLIR.MemRef.observe at observed
  cases run : Silmaril.MLIR.MemRef.run (SeaOfNodes.Memory.MLIR.MemRef.lower cells graph)
      (encodeInput input, PUnit.unit) initial with
  | mk values final =>
    cases values with
    | cons word tail =>
      cases tail
      simp only [run, Tuple.get] at observed
      exact congrArg (fun result : Word × Buffer cells =>
        ((.cons result.1 .nil : Tuple (BlockValues cells) (wordPorts cells)), result.2)) observed

private theorem encode_port {s : ValueSort} (port : Port args s) (input : Tuple (Val cells) args) :
    (encodeScalars cells input).get (scalarPort port) = encodeValue cells (input.get port) := by
  induction port with
  | head => cases input; rfl
  | tail _ ih => cases input with | cons _ rest => exact ih rest

theorem lowerActivation_run (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    runActivation graph input initial =
      let result := graph.body.denote input initial.cell
      (.cons (tailSelector result.1 (graph.stopWord input)) (.cons result.1 .nil), Buffer.mk result.2) := by
  let body := SeaOfNodes.Memory.MLIR.MemRef.lower cells graph.body
  let env : Locals (BlockValues cells) [entryPorts cells args] := (encodeInput input, PUnit.unit)
  have append := Code.runStraightLine_mapYield Op.memory (tailCode graph)
    (Silmaril.MLIR.MemRef.model cells).effect (runOp cells) (after graph)
    (fun _ _ => rfl) (tail_eval graph) body.val body.property env
  have run := congrFun append initial
  change runActivation graph input initial =
    (let (outcome, final) := Silmaril.MLIR.MemRef.run body env initial
     after graph outcome env.1 final) at run
  rw [run]
  erw [body_run graph.body input initial]
  change ((.cons (tailSelector (graph.body.denote input initial.cell).1
      ((encodeScalars cells input).get (scalarPort graph.stop)))
      (.cons (graph.body.denote input initial.cell).1 .nil) :
        Tuple (BlockValues cells) (activationPorts cells)), _) = _
  rw [encode_port graph.stop input]
  rfl

theorem observeActivation_eq_step (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    observeActivation graph input initial = (graph.step input initial.cell).map
      (fun result => (result.1, Buffer.mk result.2)) Buffer.mk := by
  unfold observeActivation Graph.step
  rw [lowerActivation_run]
  by_cases exits : (graph.body.denote input initial.cell).1 = graph.stopWord input
  · simp [tailSelector, exits]
    rfl
  · simp [tailSelector, exits]
    rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Proofs
