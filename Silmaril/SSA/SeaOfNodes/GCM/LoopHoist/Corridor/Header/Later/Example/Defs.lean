module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs

/-! # Sink a latch-dependent addition within the single-latch header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program evalOp lower)
open LoopHoist.Dominance (stage)
open Header.Example (word byte predicate Inputs input opOrder)

abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [predicate]]

/-- Binding zero feeds the backedge. In the blocked case the second
multiply also reads it. -/
def loop (blocked : Bool) : Program Inputs word word [] Schedule where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .muli))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg .head) .nil))
        (.cons (.arithmetic (.binary .muli))
          (.cons (if blocked then .output (0 : Fin 2) .head else .output (1 : Fin 2) .head)
            (.cons (.arg (.tail .head)) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (0 : Fin 4) .head) .nil
  predicate := .output (3 : Fin 4) .head
  result := .output (2 : Fin 4) .head

/-- Observe the existing chooser independently of the explicit destination. -/
def rankedCut (blocked : Bool) : Option (Nat × Nat) := do
  let g := loop blocked
  let ⟨_, binding⟩ ← findBinding 0 0 headerOrigins ((lower g).block .header)
  let cut ← chooseCut? g binding.operands binding.uses
  pure (stage cut.block, cut.cut)

/-- Show the emitted order and its observations at CF fuels three, four and five. -/
def observe (blocked : Bool) (originalCut : Nat) : Option (List String × List (Option Nat)) :=
  (moveAt? (loop blocked) 0 ⟨headerId, originalCut⟩).map fun cfg =>
    (opOrder (cfg.block .header), [3, 4, 5].map fun fuel =>
      (cfg.run evalOp fuel (input 2 4 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example
