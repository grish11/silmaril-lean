module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result saved : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

theorem chooseCfgCut?_sound
    {cfg : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    {operands : List (Point (SourceLabel carried result))} {uses : List (Use (SourceLabel carried result))}
    (selected : chooseCfgCut? cfg operands uses = some cut) :
    cut ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses cut := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  unfold chooseCfgCut? at selected
  rw [Silmaril.SSA.SeaOfNodes.GCM.Corridor.chooseSynthesized?_eq] at selected
  obtain ⟨_, _, ranked⟩ := Option.bind_eq_some_iff.mp selected
  exact LoopForest.choosePlacement_sound ranked

private theorem chooseCut_eq (operands : List (Point (SourceLabel carried result)))
    (uses : List (Use (SourceLabel carried result))) :
    chooseCut? g operands uses = (synthesizedTree? g).bind fun tree =>
      LoopForest.choosePlacement tree.1 blocks operands uses := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  exact Silmaril.SSA.SeaOfNodes.GCM.Corridor.chooseSynthesized?_eq _ _

theorem pickAndHoist?_eq :
    LoopHoist.Corridor.pickAndHoist? g index = (synthesizedTree? g).bind fun tree =>
      pickBindingAndHoist? g tree.1 index := by
  cases synthesized : synthesizedTree? g with
  | none =>
    unfold LoopHoist.Corridor.pickAndHoist? hoistBindingWith? hoistCodeWith?
    cases findBinding index 0 headerOrigins ((lower g).block .header)
    · simp
    · simp [chooseCut_eq, synthesized]
  | some tree =>
    have sameChooser : chooseCut? g = LoopForest.choosePlacement tree.1 blocks := by
      funext operands uses
      simp [chooseCut_eq, synthesized]
    rw [LoopHoist.Corridor.pickAndHoist?, sameChooser]
    rfl

private theorem existing_hoist (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output)) :
    ∃ tree, synthesizedTree? g = some tree ∧ pickBindingAndHoist? g tree.1 index = some (cut, output) := by
  rw [pickAndHoist?_eq] at picked
  exact Option.bind_eq_some_iff.mp picked

theorem refuses_otherCut {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    (selected : chooseCut? g binding.operands binding.uses = some cut)
    (outside : cut ≠ ⟨none, 0⟩) : LoopHoist.Corridor.pickAndHoist? g index = none := by
  have outsideEntry : ¬ (cut.block = none ∧ cut.cut = 0) := by
    intro atEntry
    exact outside (by cases cut; simp_all)
  simp [LoopHoist.Corridor.pickAndHoist?, hoistBindingWith?, hoistCodeWith?, found, selected, outsideEntry]

theorem pickAndHoist?_placement (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
      ∃ binding : Binding Input (carried :: Input) output.1 carried result,
        findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
        chooseCut? g binding.operands binding.uses = some cut ∧
        Legal (lower g) binding.operands binding.uses cut := by
  obtain ⟨tree, synthesized, hoisted⟩ := existing_hoist picked
  obtain ⟨atEntry, candidate, binding, found, selected, legal⟩ :=
    pickBindingAndHoist?_placement hoisted
  exact ⟨atEntry, candidate, binding, found, by simp [chooseCut_eq, synthesized, selected], legal⟩

theorem pickAndHoist?_routes (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output))
    (input : Env Input) :
    ∃ (binding : Binding Input (carried :: Input) output.1 carried result)
      (operands : Operands Input binding.args),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨output.1, binding⟩ ∧
      binding.captured? = some operands ∧
      Routes (lower g) output.2 input (evalOp binding.op (operands.eval input)) := by
  obtain ⟨_, _, hoisted⟩ := existing_hoist picked
  exact pickBindingAndHoist?_routes hoisted input

theorem pickAndHoist?_run_eq (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, hoisted⟩ := existing_hoist picked
  exact pickBindingAndHoist?_run_eq hoisted input fuel

theorem pickAndHoist?_budget (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  obtain ⟨_, _, hoisted⟩ := existing_hoist picked
  exact pickBindingAndHoist?_budget hoisted input budget

theorem pickAndHoist?_denotePart (picked : LoopHoist.Corridor.pickAndHoist? g index = some (cut, output))
    (input : Env Input) :
    (Cfg.embed output.2).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, pickAndHoist?_run_eq picked]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
