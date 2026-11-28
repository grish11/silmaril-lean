module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Split

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits

universe v w
variable {V W K J : Type w} {F : Type v} [DecidableEq K] [DecidableEq J]

omit [DecidableEq J] in
/-- A present internal block cannot occur in the accepted exit list. -/
theorem header_not_exit (graph : Graph V K F) (exits : List (Option K))
    (partition : checkExits graph exits = true) {key : K}
    (present : (graph.blocks.lookup key).isSome = true) : some key ∉ exits :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split.header_not_exit
    graph exits partition present

omit [DecidableEq J] in
/-- Collapsing external labels leaves the φ operands of internal edges intact. -/
theorem edgeReads_forScope (graph : Graph V K F) (exits : List (Option K)) (pred : Option K) (key : K) :
    GlobalSSA.edgeReads (forScope graph exits) pred key = GlobalSSA.edgeReads graph pred key :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split.edgeReads_forScope graph exits pred key

omit [DecidableEq J] in
theorem hasEdge_forScope (plan : Split.Plan V W K J) (graph : Graph V K F) (exits : List (Option K))
    (internal : some plan.header ∉ exits) :
    plan.hasEdge (forScope graph exits) = plan.hasEdge graph :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split.hasEdge_forScope plan graph exits internal

/-- Collapsing declared returns commutes with splitting an internal edge.
The forwarding label is outside the image of the declared exits. -/
theorem forScope_rewrite (plan : Split.Plan V W K J) (graph : Graph V K F) (exits : List (Option K))
    (internal : some plan.header ∉ exits) :
    forScope (plan.rewrite graph) (exits.map (Option.map plan.label)) =
      plan.rewrite (forScope graph exits) :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.OrderedExits.Split.forScope_rewrite plan graph exits internal

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
