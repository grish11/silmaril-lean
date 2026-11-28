module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence (State)
open Loop.MLIR.CF (Program evalOp lower model lower_run)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {state : State Input carried result} {output : Output Input carried result}
variable {plan : Plan} {priorities : List Nat} {origin : Nat}

theorem resolveMove?_spec {index : Nat} {cut : Point (SourceLabel carried result)}
    (accepted : resolveMove? state origin = some (index, cut, output)) :
    Header.Priority.resolve? state origin = some index ∧
      hoistCodeWith? state.cfg.entry (state.cfg.block .header) index (chooseCfgCut? state.cfg) =
        some (cut, output) := by
  obtain ⟨current, resolved, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨site, moved⟩, selected, eq⟩ := Option.bind_eq_some_iff.mp next
  change some (current, site, moved) = some (index, cut, output) at eq
  simp only [Option.some.injEq, Prod.mk.injEq] at eq
  obtain ⟨a, b, c⟩ := eq
  subst current site moved
  exact ⟨resolved, selected⟩

private theorem finish?_spec (emitted : finish? state origin = some output) :
    ∃ index, state.origins[index]? = some origin ∧
      hoistCodeWith? state.cfg.entry (state.cfg.block .header) index (chooseCfgCut? state.cfg) =
        some (⟨none, 0⟩, output) := by
  obtain ⟨⟨index, cut, moved⟩, attempted, same⟩ := Option.map_eq_some_iff.mp emitted
  change moved = output at same
  subst moved
  obtain ⟨resolved, selected⟩ := resolveMove?_spec attempted
  obtain ⟨_, _, _, rfl, _⟩ := hoistCodeWith?_spec selected
  exact ⟨index, Header.Priority.resolve?_sound resolved, selected⟩

private theorem replay?_steps (emitted : replay? g plan = some output) :
    ∃ state, Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header = some state ∧
      finish? state plan.hoistOrigin = some output :=
  Option.bind_eq_some_iff.mp emitted

theorem schedule?_replay (accepted : schedule? g priorities origin = some (plan, output)) :
    replay? g plan = some output := by
  by_cases distinct : priorities.Nodup
  · simp only [schedule?, ite_eq_left distinct] at accepted
    obtain ⟨⟨requests, state⟩, planned, finished⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨_, emitted, eq⟩ := Option.bind_eq_some_iff.mp finished
    cases eq
    simp [replay?, Header.Priority.plan?_replay planned, emitted]
  · simp [schedule?, distinct] at accepted

theorem replay?_placement (emitted : replay? g plan = some output) :
    ∃ (state : State Input carried result) (index : Nat)
      (binding : Binding Input (carried :: Input) output.1 carried result),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header = some state ∧
      state.origins[index]? = some plan.hoistOrigin ∧
      findBinding index 0 headerOrigins (state.cfg.block .header) = some ⟨output.1, binding⟩ ∧
      chooseCfgCut? state.cfg binding.operands binding.uses = some ⟨none, 0⟩ ∧
      Legal state.cfg binding.operands binding.uses ⟨none, 0⟩ := by
  obtain ⟨state, ran, finished⟩ := replay?_steps emitted
  obtain ⟨index, located, hoisted⟩ := finish?_spec finished
  obtain ⟨binding, found, selected, _, _⟩ := hoistCodeWith?_spec hoisted
  exact ⟨state, index, binding, ran, located, found, selected, (chooseCfgCut?_sound selected).2⟩

theorem replay?_routes (emitted : replay? g plan = some output) (input : Env Input) :
    ∃ (state : State Input carried result) (index : Nat)
      (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) plan.header = some state ∧
      state.origins[index]? = some plan.hoistOrigin ∧
      findBinding index 0 headerOrigins (state.cfg.block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes state.cfg output.2 input (evalOp binding.op (operands.eval input)) := by
  obtain ⟨state, ran, finished⟩ := replay?_steps emitted
  obtain ⟨index, located, hoisted⟩ := finish?_spec finished
  obtain ⟨binding, found, _, _, operands, captured, code⟩ := hoistCodeWith?_spec hoisted
  obtain ⟨_, headerOnly, _⟩ := Header.Sequence.run?_header ran
  have exit : state.cfg.block .exit = .terminator (.ret (.cons .here .nil)) := by
    rw [headerOnly]
    rfl
  have routed := emitHeader_routes exit binding found operands captured input
  rw [← code] at routed
  exact ⟨state, index, binding, operands, ran, located, found, captured, routed⟩

theorem replay?_run_eq (emitted : replay? g plan = some output) (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨state, _, _, _, ran, _, _, _, routed⟩ := replay?_routes emitted input
  have reordered : Header.Sequence.schedule? g plan.header = some state.cfg := by
    simp [Header.Sequence.schedule?, ran]
  exact (routes_run_eq routed fuel).trans (Header.Sequence.schedule?_run_eq reordered input fuel)

theorem replay?_budget (emitted : replay? g plan = some output) (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (replay?_run_eq emitted input _).trans (lower_run g input budget)

theorem replay?_denotePart (emitted : replay? g plan = some output) (input : Env Input) :
    (Cfg.embed output.2).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, replay?_run_eq emitted]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder
