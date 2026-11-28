module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Ty ValueSort sortValue)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Iteration.Preheader (normalize normalize_entry normalize_returns)
open GVN.Cyclic.Iteration.Preheader.Theta
open Loop (ThetaOpcode lowerFlow thetaRuntime)
open Pure.SubZero (Opcode model)
open Silmaril.SSA.RVSDG (Address extend)
open Silmaril.SSA.RVSDG.NestedTheta (Graph MonadicModel NodeLabel Term)
open Silmaril.SSA.RVSDG.NestedTheta.Partial (observe)

section Prefix

variable {args outs head : List (Ty Unit)} {past sigs tail : List (List (Ty Unit))}

private def nodeWiring (graph : Graph (ThetaOpcode Opcode) args past sigs outs) (i : Fin sigs.length) :
    NodeLabel (ThetaOpcode Opcode) × List Address :=
  let node := graph.nodes i
  (node.label, node.inputs.addresses)

/-- The numbered table inherits the head of the ordered term, with
exactly its opcode, signature and ordered input wires. -/
private theorem bind_zero
    (node : Silmaril.SSA.RVSDG.NestedTheta.Node (ThetaOpcode Opcode) args past head)
    (body : Silmaril.SSA.RVSDG.NestedTheta.Children (Term (ThetaOpcode Opcode)) node)
    (rest : Term (ThetaOpcode Opcode) args (past ++ [head]) tail outs) :
    nodeWiring (Term.bind node body rest).toGraph ⟨0, Nat.zero_lt_succ _⟩ =
      (node.label, node.inputs.addresses) := by
  change nodeWiring (rest.toGraph.prepend node (fun j => (body j).toGraph)) _ = _
  cases rest.toGraph
  rfl

private theorem bind_succ
    (node : Silmaril.SSA.RVSDG.NestedTheta.Node (ThetaOpcode Opcode) args past head)
    (body : Silmaril.SSA.RVSDG.NestedTheta.Children (Term (ThetaOpcode Opcode)) node)
    (rest : Term (ThetaOpcode Opcode) args (past ++ [head]) tail outs) (i : Fin tail.length) :
    nodeWiring (Term.bind node body rest).toGraph i.succ = nodeWiring rest.toGraph i := by
  change nodeWiring (rest.toGraph.prepend node (fun j => (body j).toGraph)) _ = _
  cases rest.toGraph
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem lowerFlow_entry (flow : Dataflow Opcode args past sigs)
    (left right : Term (ThetaOpcode Opcode) args (extend past sigs) (head :: tail) outs)
    (entry : nodeWiring left.toGraph ⟨0, Nat.zero_lt_succ _⟩ =
      nodeWiring right.toGraph ⟨0, Nat.zero_lt_succ _⟩)
    (i : Fin (sigs ++ head :: tail).length) (before : i.val ≤ sigs.length) :
    nodeWiring (lowerFlow flow left).toGraph i = nodeWiring (lowerFlow flow right).toGraph i := by
  induction flow with
  | nil =>
    have zero : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext (Nat.eq_zero_of_le_zero before)
    rw [zero]
    exact entry
  | @cons _ more _ out _ _ _ ih =>
    revert before
    refine Fin.cases ?_ (fun j before => ?_) i
    · intro _
      simp only [lowerFlow]
      let zero : Fin (([.value out] : List (Ty Unit)) :: (more ++ head :: tail)).length :=
        ⟨0, Nat.zero_lt_succ _⟩
      change nodeWiring _ zero = nodeWiring _ zero
      dsimp only [zero]
      rw [bind_zero, bind_zero]
    · simp only [lowerFlow, bind_succ]
      exact ih left right entry j (Nat.le_of_succ_le_succ before)

end Prefix

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}
variable (loop : Native inputs carried entrySigs headerSigs out) (input : Inputs model inputs)

set_option backward.isDefEq.respectTransparency false in
theorem emit_entry : entryPrefix (emit loop) = entryPrefix loop.lowerTheta := by
  have kept := normalize_entry loop
  let rewritten := (normalize loop).rewrite.graph
  change rewritten.preheader = loop.preheader ∧ rewritten.phiInputs .entry = loop.phiInputs .entry at kept
  unfold entryPrefix
  congr 1
  funext i
  change nodeWiring (emit loop) _ = nodeWiring loop.lowerTheta _
  unfold emit Loop.Graph.lowerTheta Loop.Graph.lowerThetaTerm
  change nodeWiring (lowerFlow rewritten.preheader _).toGraph _ = _
  rw [kept.1]
  dsimp only [rewritten] at kept
  apply lowerFlow_entry loop.preheader
  · rw [bind_zero, bind_zero]
    rw [kept.2]
    rfl
  · exact Nat.le_of_lt_succ i.isLt

theorem emit_returns_iff (value : sortValue model.value out) :
    (emit loop).Returns (thetaRuntime model) input (.cons value .nil) ↔
      loop.lowerTheta.Returns (thetaRuntime model) input (.cons value .nil) := by
  let rewritten := (normalize loop).rewrite.graph
  exact (rewritten.lowerTheta_returns_iff model input value).symm.trans
    ((normalize_returns loop input value).trans (loop.lowerTheta_returns_iff model input value))

theorem emit_observe :
    observe (MonadicModel.ofRuntime (thetaRuntime model)) (emit loop) input =
      observe (MonadicModel.ofRuntime (thetaRuntime model)) loop.lowerTheta input := by
  apply Part.ext
  intro result
  cases result with
  | cons value tail =>
    cases tail
    rw [← Part.eq_some_iff, ← Part.eq_some_iff]
    let rewritten := (normalize loop).rewrite.graph
    exact (rewritten.lowerTheta_observe_eq_some model input value).symm.trans
      ((normalize_returns loop input value).trans (loop.lowerTheta_observe_eq_some model input value))

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta
