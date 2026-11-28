module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example.Defs

/-! # Make a dependent consumer available after the first hoist -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program evalOp)
open Corridor.Example (word byte predicate Inputs input entrySigs)

abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [predicate], [byte]]

/-- The consumer uses the saved producer plus the stride, or a value
derived from the latch in the varying case. -/
def loop (varying : Bool) : Program Inputs word word entrySigs Schedule where
  preheader := (Corridor.Example.loop false).preheader
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (.output (1 : Fin 2) .head)
            (.cons (if varying then .output (0 : Fin 2) .head else .arg (.tail (.tail .head))) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
            (.cons (.arithmetic (.binary .addi))
              (.cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)) .nil))))
  phiInputs
    | .entry => (Corridor.Example.loop false).phiInputs .entry
    | .backedge => .cons (.output (4 : Fin 5) .head) .nil
  predicate := .output (3 : Fin 5) .head
  result := .output (2 : Fin 5) .head

def first : AfterReorder.Plan := ⟨[⟨3, 0⟩], 1⟩

/-- Observe the remaining origins, current binding index, operand cuts
and the intermediate CFG's observations at fuels three, four and five. -/
def observe (varying : Bool) :
    Option (List Nat × Nat × List Nat × List (Option Nat)) :=
  (prepare? (loop varying) first 2).map fun prepared =>
    (prepared.origins, prepared.index, prepared.consumer.operands.map Point.cut,
      [3, 4, 5].map fun fuel =>
        (prepared.intermediate.2.run evalOp fuel (input 2 10 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example
