module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Thms

/-! # Pack a typed flat CFG with a supplied entry record -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

variable {κ : Type (u + 1)} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n blocks exits : Nat} {β : BoundCtx (Ty κ) n}
  {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ} {g : FiniteCFG Φ blocks exits n}

/-- Decode the exact entry context around the actual packed dispatcher.
Each block sees its own parameter above the shared decoded context. -/
def Program.ofCFGEntry (h : g.HasType β R D) :
    Program Φ (Region.packedInputType β.toList) (Region.packedExitType (List.ofFn D)) :=
  ⟨(FiniteCFG.packedExecutionRegion h).packInputsDestructure β.toList,
    (FiniteCFG.packedExecution_context_valueBranches h).hasType.packInputsDestructure⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
