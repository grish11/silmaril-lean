module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! # Execute the numbered table with partial primitives -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {m : Model.{u,v,w} Op}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A computable primitive table with the same successful observations as
the partial model. It supplies the decision for which primitive calls return. -/
structure Actions (m : Model.{u,v,w} Op) where
  primitive {ins outs : Ports (PortType V S)} : Op ins outs → Tuple m.Val ins → Option (Tuple m.Val outs)
  agrees {ins outs : Ports (PortType V S)} (op : Op ins outs) (input : Tuple m.Val ins) :
    Part.ofOption (primitive op input) = m.primitive op input

/-- Execute the very same primitive when its domain has a computable decision. -/
def Actions.ofDecidable (m : Model.{u,v,w} Op)
    (domain : {ins outs : Ports (PortType V S)} → (op : Op ins outs) → (input : Tuple m.Val ins) →
      Decidable (m.primitive op input).Dom) : Actions m where
  primitive op input := @Part.toOption _ (m.primitive op input) (domain op input)
  agrees op input := @Part.of_toOption _ (m.primitive op input) (domain op input)

def kindEval (actions : Actions m) (fuel : Nat) : KindEvaluator Op m.Val
  | _, _, .base (.simple op), _, input => actions.primitive op input
  | _, _, .base (.gamma _), child, .cons tag input => child tag.down input
  | _, _, .theta _, child, input => iterate (child (0 : Fin 1)) (fun tag => tag.down.val == 1) fuel input

/-- Run the actual numbered table. The bound is per θ invocation. A
`none` result at that bound only says execution produced no result there. -/
def run (actions : Actions m) (g : Graph Op args [] sigs outs) (fuel : Nat)
    (input : Tuple m.Val args) : Option (Tuple m.Val outs) :=
  g.evalWith (kindEval actions fuel) input PUnit.unit

end Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable
