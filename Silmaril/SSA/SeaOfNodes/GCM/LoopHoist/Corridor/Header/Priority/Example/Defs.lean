module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs

/-! # A priority whose current index changes after the previous move -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program evalOp)
open Header.Example (word byte predicate Inputs input opOrder)

abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [predicate]]

/-- The feedback multiply reads the preceding addition. The exit
multiply and comparison are independent of the preceding bindings. -/
def loop : Program Inputs word word [] Schedule where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .muli))
        (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil))
        (.cons (.arithmetic (.binary .muli))
          (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (1 : Fin 4) .head) .nil
  predicate := .output (3 : Fin 4) .head
  result := .output (2 : Fin 4) .head

/-- Show replay coordinates, emitted opcode order, and results at CFG
fuels three, four and five. -/
def observe (priorities : List Nat) :
    Option (List (Nat × Nat) × List String × List (Option Nat)) :=
  (schedule? loop priorities).map fun (requests, cfg) =>
    (requests.map (fun request => (request.binding, request.cut)), opOrder (cfg.block .header),
      [3, 4, 5].map fun fuel =>
        (cfg.run evalOp fuel (input 1 3 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example
