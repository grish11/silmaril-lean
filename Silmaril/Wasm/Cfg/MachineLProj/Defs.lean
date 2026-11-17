module

public import Silmaril.Wasm.Cfg.MachineL.Defs

@[expose] public section

/-!
# Projecting the logged machine to `MStepC`: definitions

`PopFit f k ls stk`: leaving `k` sequences from the label frames `ls` with the stack `stk` (bottom
first), each left frame's block type has arities (`Binaryen.arity`), and the stack at each level
has at most that frame's result arity. On such stacks the logged machine's native frame popping
(`popN`, which keeps the top `nr` values) is `MStepC`'s Core popping (`popL`, which keeps the
whole stack). Typed code leaves an arm normally with exactly its result arity.

Theorems in `Silmaril.Wasm.Cfg.MachineLProj.Thms`.
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core

/-- **The stack fits each level left**: leaving `k` sequences, each left frame's block type has
arities, and the stack at that level has at most its result arity. -/
def PopFit (f : Frame) : Nat → List LFrame → List Val → Prop
  | 0, _, _ => True
  | _ + 1, [], _ => False
  | k + 1, L :: ls, stk => ∃ np nr, Binaryen.arity f L.bt = some (np, nr) ∧ stk.length ≤ nr ∧
      PopFit f k ls (L.outer ++ stk)

end Silmaril.Wasm.Cfg.MachineL
