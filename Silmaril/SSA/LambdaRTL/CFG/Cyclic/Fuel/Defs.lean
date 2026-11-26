module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Defs

/-! Executable finite budgets for the existing full-table λRTL step. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe v w

variable {V K α : Type w} {F : Type v}

def toPartModel (m : Model F Option α) : Model F Part α where
  unit := m.unit
  pair := m.pair
  inl := m.inl
  inr := m.inr
  unpair a := Part.ofOption (m.unpair a)
  split a := Part.ofOption (m.split a)
  app op a := Part.ofOption (m.app op a)
  abort a := Part.ofOption (m.abort a)

variable [DecidableEq V] [DecidableEq K]

/-- Spend one unit on the actual cyclic step, including the lookup that
classifies a transfer to an absent label as an exit. -/
def runFromFuel (m : Model F Option α) (table : List (K × Block V K F)) :
    Nat → Transfer V K α → Option (Transfer V K α)
  | 0, _ => none
  | fuel + 1, current =>
    match step m table current with
    | none => none
    | some (.inl result) => some result
    | some (.inr next) => runFromFuel m table fuel next

/-- The entry executes once. The budget counts transfer resolution after it. -/
def runFuel (m : Model F Option α) (cfg : CFG V K F) (fuel : Nat) (store : V → α) :
    Option (Transfer V K α) :=
  cfg.entry.exec m (fun label packet next => some (label, packet, next)) store >>=
    runFromFuel m cfg.blocks fuel

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
