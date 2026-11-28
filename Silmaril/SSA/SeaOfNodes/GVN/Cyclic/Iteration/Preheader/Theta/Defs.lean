module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! Emit the actual normalized native graph through the numbered θ lowering. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta

open Builder.Preheader (Native)
open Diamond (Ty ValueSort dataPorts)
open Pure.SubZero (Opcode)
open RVSDG.NestedTheta (NodeLabel)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

abbrev Program (inputs carried : List (ValueSort Unit)) (entrySigs : List (List (Ty Unit)))
    (out : ValueSort Unit) :=
  RVSDG.NestedTheta.Graph (Loop.ThetaOpcode Opcode) (dataPorts inputs) [] (Loop.thetaSigs inputs carried entrySigs out) [.value out]

/-- Emit one θ after running the full native normalization, on the
original input and result interface. -/
def emit (loop : Native inputs carried entrySigs headerSigs out) :
    Program inputs carried entrySigs out :=
  (normalize loop).rewrite.graph.lowerTheta

/-- Inspect the actual numbered preheader nodes and the θ entry node.
Keep their typed labels and all ordered input addresses. -/
def entryPrefix (program : Program inputs carried entrySigs out) :
    List (NodeLabel (Loop.ThetaOpcode Opcode) × List RVSDG.Address) :=
  List.ofFn fun (i : Fin (entrySigs.length + 1)) =>
    let node := program.nodes ⟨i.val, by
      have bound := i.isLt
      simp only [Loop.thetaSigs, List.length_append, List.length_cons, List.length_nil]
      omega⟩
    (node.label, node.inputs.addresses)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta
