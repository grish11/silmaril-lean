module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Coverage
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Proofs

open SeaOfNodes.Diamond (ValueSort Val dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple Wires Locals)
open RVSDG.NestedTheta (Graph Term)
open Join (Opcode)
open Join.Finite (lastBank lastBank_read)
open Tail.Diamond (thenBase_eval)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {past : List (List (Diamond.Ty Width))}
variable {outs : List (Diamond.Ty Width)}
variable (childSigs : Fin 2 → List (List (Diamond.Ty Width)))
variable (children : ∀ i, Graph (Opcode Op) (dataPorts regs) [] (childSigs i) outs)

private theorem choose_eval (wires : Wires (dataPorts regs) past Tag) (fuel : Nat)
    (input : Bank (regs := regs) model) (locals : Locals (Val Word) past) :
    (choose childSigs children wires).eval (Join.model model) fuel input locals =
      (children ((wires.read input locals).get .head).down).run (Join.model model) fuel input := by
  let gamma : RVSDG.NestedTheta.Kind (Opcode Op) (.control 2 :: dataPorts regs) outs :=
    .base (.gamma 0)
  change (gamma.eval (Join.model model) fuel
    (fun i bank => by
      change Fin 2 at i
      exact (children i).toTerm.run (Join.model model) fuel bank)
    ((gammaNode (outs := outs) (wires.get .head) childSigs).inputs.read input locals)).bind
    (fun output => some ((lastBank past outs).read input (locals.snoc output))) = _
  rw [gamma_inputs, ← read_get model]
  let side := ((wires.read input locals).get .head).down
  change ((children side).toTerm.run (Join.model model) fuel input).bind (fun output =>
    some ((lastBank past outs).read input (locals.snoc output))) = _
  rw [Graph.run_toTerm]
  cases (children side).run (Join.model model) fuel input with
  | none => rfl
  | some output =>
    change some ((lastBank past outs).read input (locals.snoc output)) = some output
    rw [lastBank_read model]

theorem attach_run (test : Selector regs) (fuel : Nat) (input : Bank (regs := regs) model) :
    (attach test childSigs children).run (Join.model model) fuel input =
      let selected := ((test.2.toGraph.run (Join.model model) input).get .head).down
      (children selected).run (Join.model model) fuel input := by
  rw [attach, ← Graph.run_toTerm, Term.toTerm_toGraph, RVSDG.Term.run_toGraph]
  exact thenBase_eval (Join.model model) fuel test.2 _ input PUnit.unit
    (fun packet => (children (packet.get .head).down).run (Join.model model) fuel input)
    (fun wires locals => choose_eval childSigs children wires fuel input locals)

variable {result : Width} {p : Program Op regs (.data result)}
variable [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)} {target : Target regs result}

theorem lower_run_arm (checked : Checked model p facts) (fuel : Nat)
    (input : Bank (regs := regs) model) :
    (lower checked).2.run (Join.model model) fuel input =
      (arms checked (index (@decide _ (decideTupleCovers facts input)))).2.run (Join.model model) fuel input := by
  change (attach (selector facts) (fun i => (arms checked i).1) (fun i => (arms checked i).2)).run
    (Join.model model) fuel input = _
  rw [attach_run, selector_run]
  rfl

private theorem specialized_of_compile (success : compile p facts = .ok target) :
    ∃ checked : Checked model p facts,
      target = lower checked ∧ Bypass.Numbered.compile model p facts = some (Bypass.Numbered.lower checked) := by
  cases admitted : Backends.Worklist.admit model p facts with
  | error reason => simp [compile, admitted, Except.map] at success
  | ok checked =>
    have simultaneous := (Backends.Worklist.admit_eq_simultaneous model p facts).symm.trans admitted
    have eq : lower checked = target := by simpa [compile, admitted, Except.map] using success
    exact ⟨checked, eq.symm, by
      rw [Bypass.Numbered.compile, Dispatch.check, simultaneous]
      rfl⟩

theorem compile_run (success : compile p facts = .ok target) (fuel : Nat)
    (input : Bank (regs := regs) model) :
    target.2.run (Join.model model) fuel input =
      (p.source.runFrom model (3 * fuel + 2) 0 input).map (fun value => .cons value .nil) := by
  obtain ⟨checked, rfl, specialized⟩ := specialized_of_compile success
  rw [lower_run_arm]
  cases covered : @decide _ (decideTupleCovers facts input)
  · exact TwoBackedges.Numbered.lower_run p model fuel input
  · exact Bypass.Numbered.compile_run specialized
      (@of_decide_eq_true (TupleCovers facts input) (decideTupleCovers facts input) covered) fuel

theorem compile_returns_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) (value : Word result) :
    target.2.Returns (Join.model model) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value := by
  obtain ⟨checked, rfl, specialized⟩ := specialized_of_compile success
  simp only [Graph.Returns, lower_run_arm]
  cases covered : @decide _ (decideTupleCovers facts input)
  · exact TwoBackedges.Numbered.returns_iff p model input value
  · exact Bypass.Numbered.compile_returns_iff specialized
      (@of_decide_eq_true (TupleCovers facts input) (decideTupleCovers facts input) covered) value

theorem compile_noReturn_iff (success : compile p facts = .ok target) (input : Bank (regs := regs) model) :
    (∀ fuel, target.2.run (Join.model model) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value := by
  obtain ⟨checked, rfl, specialized⟩ := specialized_of_compile success
  simp only [lower_run_arm]
  cases covered : @decide _ (decideTupleCovers facts input)
  · exact TwoBackedges.Numbered.noReturn_iff p model input
  · exact Bypass.Numbered.compile_noReturn_iff specialized
      (@of_decide_eq_true (TupleCovers facts input) (decideTupleCovers facts input) covered)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Proofs
