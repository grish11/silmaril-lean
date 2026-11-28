module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RegisterRename.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.RegisterRename

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open CFG.Cyclic.RoundTrip (renameGraph)

universe v w
variable {V W K : Type w} {F : Type v} [DecidableEq V] [DecidableEq W] [DecidableEq K]

/-- Exact scoped elaboration is invariant under register renaming. First
matches, branch positions and the order of the capture slots are preserved. -/
theorem elaborateAt_rename (rename : V ↪ W) (g : CFG V K F) (exits : List K) {n : Nat}
    (captures : Fin n → V) (count : Nat) (len : g.blocks.length = count)
    (renamedLen : (renameGraph rename g).blocks.length = count) :
    elaborateAt (renameGraph rename g) exits (rename ∘ captures) count renamedLen =
      elaborateAt g exits captures count len :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.RegisterRename.elaborateAt_rename rename g exits captures count len renamedLen

end Silmaril.Isotope.Bridge.NamedFlat
