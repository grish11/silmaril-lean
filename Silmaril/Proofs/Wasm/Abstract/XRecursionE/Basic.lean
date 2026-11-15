module

public import Silmaril.Wasm.Abstract.XRecursionE.Defs

/-!
Proofs for `Silmaril.Wasm.Abstract.XRecursionE.Thms`: the closure is a fixpoint and keeps the
store's functions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XRecursionE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.XRecursionE

variable {H : Type}

theorem closedCallXE_eq_bodyCallXE : (closedCallXE : CallRel H) = bodyCallXE closedCallXE :=
  (OrderHom.map_lfp bodyCallXEOp).symm

/-- The closure keeps the store's functions. -/
theorem closedCallXE_funcs :
    ∀ (s : Store H) a args out, closedCallXE s a args out → out.1.funcs = s.funcs := by
  have : (closedCallXE : CallRel H) ≤ fun s _ _ out => out.1.funcs = s.funcs := by
    refine OrderHom.lfp_le _ ?_
    rintro s a args out ⟨fi, fn, ps, rs, f₂, -, -, -, hb⟩
    exact evalOXE_funcs (fun _ _ _ _ h => h) hb
  exact fun s a args out h => this s a args out h

end Silmaril.Proofs.Wasm.Abstract.XRecursionE
