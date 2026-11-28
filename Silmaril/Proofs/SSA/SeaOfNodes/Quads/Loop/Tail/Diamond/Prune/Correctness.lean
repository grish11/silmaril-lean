module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Proofs

open SeaOfNodes.Diamond (Dataflow Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Port Tuple Wires extend)
open RVSDG.NestedTheta (Term iterate)
open Join (Block model)
open Join.Finite (lastBank lastBank_read)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask) (m : Model.{u, v, w} Op)

theorem header_projection_agrees {body : Block Op regs} (projected : HeaderProjection body mask)
    (old : Bank (regs := regs) m) :
    projected.headerBank m (mask.project old) = body.eval m old := by
  unfold HeaderProjection.headerBank
  rw [mask.projected_flow m old (past := []) PUnit.unit _ _ projected.flow_eq]
  rw [mask.projected_wires m old _ _ _ projected.outgoing_eq]
  exact (CFG.compileBlock_read (past := []) body m old PUnit.unit (initial regs)).trans
    (congrArg (Block.eval body m) (read_initial m old))

theorem header_agrees (old : Bank (regs := regs) m) :
    checked.headerBank m (mask.project old) = (src p.header).body.eval m old :=
  header_projection_agrees m checked.toHeaderProjection old

theorem trace_agrees (fuel : Nat) (old : Bank (regs := regs) m) :
    checked.trace m fuel (mask.project old) = p.trace m fuel old := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    have rest := ih (p.nextBank m old)
    simp only [Checked.trace, Program.trace, Program.nextBank] at rest
    simp only [Checked.trace, Program.trace, traceFrom, header_agrees checked m, Program.selected,
      Program.nextBank, rest]; rfl

theorem lowerFlow_eval {args results : List (Ty Data)} {past sigs : List (List (Ty Data))}
    (flow : Dataflow Op args past sigs) (wires : Wires args (extend past sigs) results)
    (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (lowerFlow flow wires).eval (model m) input locals = wires.read input (flow.eval m input locals) := by
  induction flow with
  | nil => rfl
  | cons op operands rest ih =>
    exact ih wires (locals.snoc (.cons (m.run op (operands.read input locals)) .nil))

private theorem projectPacket_read {args : List (Ty Data)} {past : List (List (Ty Data))}
    (wires : Wires args past (bodyPorts regs))
    (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Wires.read (projectPacket mask wires) input locals = projectPacket mask (wires.read input locals) := by
  cases wires with
  | cons tag bank =>
    exact congrArg (Tuple.cons (SeaOfNodes.Diamond.read m tag input locals))
      (mask.project_read m input locals bank)

theorem routeProjectedWith_eval {args : List (Ty Data)} {past : List (List (Ty Data))}
    (again : Port (dataPorts regs) (.value .predicate)) (wires : Wires args past (dataPorts regs))
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (routeProjectedWith again mask wires).eval (model m) fuel input locals =
      some (RVSDG.Theta.bodyResult (model m) ((wires.read input locals).get again).down
        (mask.project (wires.read input locals))) := by
  let bank := wires.read input locals
  change some (Wires.read (projectPacket mask (lastBank past (bodyPorts regs))) input
    (locals.snoc ((model m).run (.route (.test again (.take 1) (.take 0))) bank))) = _
  rw [projectPacket_read m, lastBank_read m]
  change some (projectPacket mask ((model m).run (.route (.test again (.take 1) (.take 0))) bank)) =
    some (RVSDG.Theta.bodyResult (model m) (bank.get again).down (mask.project bank))
  by_cases h : (bank.get again).down = true <;>
    simp [model, Join.Choice.eval, RVSDG.Theta.bodyResult, projectPacket, h] <;> rfl

theorem activation_agrees (fuel : Nat) (old : Bank (regs := regs) m) :
    checked.thetaBody.run (model m) fuel (mask.project old) =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down
        (mask.project (p.nextBank m old))) := by
  let inspect (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down (mask.project bank))
  change (thenBase _ _).eval _ _ _ _ = inspect (p.nextBank m old)
  erw [thenBase_eval (observe := fun bank => inspect (p.tail.eval m (p.stage.eval m bank)))]
  · erw [lowerFlow_eval]
    change inspect (p.tail.eval m (p.stage.eval m (checked.headerBank m (mask.project old)))) = _
    rw [header_agrees checked m]
    rfl
  · intro header locals
    exact p.afterHeader_eval m header (routeProjected p mask) fuel (mask.project old) locals
      inspect (fun wires locals' => routeProjectedWith_eval (mask := mask) m p.again wires fuel (mask.project old) locals')

private theorem iterate_project (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    iterate (checked.thetaBody.run (model m) bodyFuel) (fun tag => tag.down.val == 1)
      fuel (mask.project old) =
      (iterate (p.thetaBody.run (model m) bodyFuel) (fun tag => tag.down.val == 1) fuel old).map mask.project := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    simp only [iterate, activation_agrees checked m, p.activation_run m, RVSDG.Theta.bodyResult]
    by_cases h : ((p.nextBank m old).get p.again).down = true
    · simp [h]
      exact ih (p.nextBank m old)
    · simp [h]; rfl

theorem thetaThenReturn_eval {past sigs : List (List (Ty Data))}
    (body : Term (Join.Opcode Op) (dataPorts mask.kept) [] sigs (bodyPorts mask.kept))
    (result : Port (dataPorts mask.kept) (.value out))
    (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (thetaThenReturn mask body result wires).eval (model m) fuel input locals =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel (mask.project (wires.read input locals))).map
        (fun bank => .cons (bank.get result) .nil) := by
  change (iterate (body.run (model m) fuel) _ fuel (Wires.read (mask.project wires) input locals)).bind
    (fun bank => some (Wires.read (.cons ((lastBank past (dataPorts mask.kept)).get result) .nil)
      input (locals.snoc bank))) = _
  rw [mask.project_read m]
  cases iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel
      (mask.project (wires.read input locals)) with
  | none => rfl
  | some bank =>
    change some (Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank past (dataPorts mask.kept)).get result)
      input (locals.snoc bank)) .nil) = _
    rw [← read_get, lastBank_read m]
    rfl

private theorem graph_run (fuel : Nat) (input : Bank (regs := regs) m) :
    checked.lower.run (model m) fuel input =
      (iterate (checked.thetaBody.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel (mask.project ((src entry).body.eval m input))).map
        (fun bank => .cons (bank.get checked.result) .nil) := by
  rw [Checked.lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold Checked.lowerTerm Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iterate (checked.thetaBody.run (model m) fuel) (fun tag => tag.down.val == 1)
      fuel (mask.project bank)).map (fun done => .cons (done.get checked.result) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact thetaThenReturn_eval m checked.thetaBody checked.result wires fuel input locals

theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) m) :
    checked.lower.run (model m) fuel input = p.lower.run (model m) fuel input := by
  rw [graph_run checked m, p.lower_iterate m, iterate_project checked m]
  cases iterate (p.thetaBody.run (model m) fuel) (fun tag => tag.down.val == 1)
      fuel ((src entry).body.eval m input) with
  | none => rfl
  | some bank =>
    exact congrArg (fun x => some (Tuple.cons (F := Val m.value) (t := .value out) x .nil))
      (mask.project_get bank p.result checked.result checked.result_eq)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Proofs
