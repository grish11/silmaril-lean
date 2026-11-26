module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.InstructionMap.Thms
public import Silmaril.Semantics.ITree.Signature.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Signature

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction

open CategoryTheory

universe u v w a

/-- Renaming the opcodes in a region is execution under primitive
precomposition. The input environment and transfers are unchanged. -/
theorem region_mapInstr {Events : Type u → Type u} {Φ : Type v} {Ψ : Type w} {α : Type a}
    (f : Φ → Ψ) (instr : Primitive Events Ψ α) (env : Semantics.Env α) (r : Region Φ) :
    region instr env (r.mapInstr f) = region (fun op => instr (f op)) env r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.region_mapInstr f instr env r

/-- Reindex an actual weak execution by interpreting each primitive through
the same event morphism. The region and its ordered transfers stay fixed. -/
theorem region_reindex {S T : Silmaril.Elgot.ITree.Signature.{u}} {Φ : Type v} {α : Type w}
    (f : S ⟶ T) (instr : Primitive S.Event Φ α) (env : Env α) (r : Region Φ) :
    f.tree id (region instr env r) = region (fun op arg => f.tree id (instr op arg)) env r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.region_reindex f instr env r

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction
