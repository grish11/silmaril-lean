module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Thms
public import Silmaril.Logic.Reachability.Derivation.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature}
namespace Embedding
variable {k : Nat} {Γ : Fin k → Sg.S}

/-- Realize a sorted block using actual dependent updates at precisely its fresh
stock names. The original outer stock supplies every unmodified coordinate. -/
noncomputable def realizeBlock (e : Embedding Γ) (M : FOL.Structure Sg)
    (a : StockAssignment M) : (xs : List Sg.S) → BlockAssignment M xs → StockAssignment M
  | [], _ => a
  | s :: xs, b => (e.extendBlock xs).rebind M s (e.realizeBlock M a xs b.2) b.1

end Embedding
end Silmaril.Logic.Reachability.Derivation.FirstOrder
