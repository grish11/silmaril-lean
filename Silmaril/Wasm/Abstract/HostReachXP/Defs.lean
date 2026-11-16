module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Games.Abstract.CloseReach.Defs

/-!
# The canonical closure with reach: definitions

`reachXP`: the call `⟨a, (vs, s)⟩` of a Wasm function reaches the internal call `z` after the open
prefix `l.map OCall.lift`, when its body reaches `z` after the logged prefix `l` (`ReachLXP`).

With it, `Shape.closeR wasmHOpenXP reachXP` closes the canonical open module, resolving a callee's
trap or divergence at the point the body reaches the call (`Silmaril.Games.Abstract.CloseReach`).
The theorems (`Silmaril.Wasm.Abstract.HostReachXP.Thms`) show that this is `wasmEvFunXP`: the
cut behaviours of `wasmHOpenXP` already give every reach (`reachLXP_cut`), so reach adds nothing
to `Shape.close` there.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Reach of the canonical open module**: a Wasm body reaches the internal call `z` after the
logged prefix `l` (in a function with a function type). -/
def reachXP : (wasmHShape H).ReachRel := fun x u z =>
  ∃ (fi : FuncInst H) (fn : Func) (l : List (OCall H)), x.2.2.funcs[x.1]? = some fi ∧
    fi.code = .wasm fn ∧ (∃ ps rs, Validation.DefType.funcType? fi.type = some (ps, rs)) ∧
    ReachLXP x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) l z ∧
    u = l.map OCall.lift

end Silmaril.Wasm.Abstract
