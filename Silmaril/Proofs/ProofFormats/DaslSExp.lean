module

public import Silmaril.ProofFormats.DaslSExp.Defs

public section

namespace Silmaril.Proofs.ProofFormats.DaslSExp

open Silmaril.Formats (SExp)
open Silmaril.Logic.Smt (SE)
open Silmaril.ProofFormats.DaslSExp

mutual
theorem to_of (form : SE) : toLogic (ofLogic form) = form := by
  cases form with
  | atom => rfl
  | list items =>
    change SE.list (List.ofFn (toLogic ∘ (ofLogicItems items).get)) = .list items
    rw [← List.map_ofFn, List.ofFn_get, to_of_items]
termination_by structural form

theorem to_of_items (items : List SE) : (ofLogicItems items).map toLogic = items := by
  cases items with
  | nil => rfl
  | cons head rest => simp [ofLogicItems, to_of head, to_of_items rest]
termination_by structural items
end

end Silmaril.Proofs.ProofFormats.DaslSExp
