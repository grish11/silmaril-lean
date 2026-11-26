module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.Semantics.ITree.Signature.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Signature

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction

open CategoryTheory
open Silmaril.Elgot.ITree (Signature)

universe u v w

/-- Reindex an actual weak execution by interpreting each primitive through
the same event morphism. The region and its ordered transfers stay fixed. -/
theorem region_reindex {S T : Signature.{u}} {Φ : Type v} {α : Type w}
    (f : S ⟶ T) (instr : Primitive S.Event Φ α) (env : Env α) (r : Region Φ) :
    f.tree id (region instr env r) = region (fun op arg => f.tree id (instr op arg)) env r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.region_reindex f instr env r

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction
