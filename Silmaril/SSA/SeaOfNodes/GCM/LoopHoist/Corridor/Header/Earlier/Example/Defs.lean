module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs

/-! # Move a latch-dependent addition across two retained bindings -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (Program evalOp lower)
open LoopHoist.Dominance (stage)
open Header.Example (word byte predicate Inputs input opOrder)

abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [byte], [predicate]]

/-- Nominate binding 3. It uses binding 0, or binding 1 when the earlier
crossing is blocked. Binding 2 uses binding 1 in both cases. -/
def loop (blocked : Bool) : Program Inputs word word [] Schedule where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .muli))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg .head) .nil))
        (.cons (.arithmetic (.binary .muli))
          (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil))
          (.cons (.arithmetic (.binary .addi))
            (.cons (if blocked then .output (1 : Fin 3) .head else .output (0 : Fin 3) .head)
              (.cons (.arg (.tail (.tail .head))) .nil))
            (.cons (.ult word)
              (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil)) .nil))))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (3 : Fin 5) .head) .nil
  predicate := .output (4 : Fin 5) .head
  result := .output (2 : Fin 5) .head

/-- Report the original destination, the emitted opcode order, and the
emitted program's results at CF fuels three, four and five. -/
def observe (blocked : Bool) :
    Option ((Nat × Nat) × List String × List (Option Nat)) :=
  (pickAndMove? (loop blocked) 3).map fun (cut, cfg) =>
    ((stage cut.block, cut.cut), opOrder (cfg.block .header), [3, 4, 5].map fun fuel =>
      (cfg.run evalOp fuel (input 2 6 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example
