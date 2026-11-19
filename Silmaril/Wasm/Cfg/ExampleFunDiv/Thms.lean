module

public import Silmaril.Wasm.Cfg.ExampleFunDiv.Defs
public import Silmaril.Wasm.Cfg.FunctionCfg.Thms
public import Silmaril.Wasm.Abstract.XDiverge.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleFunDiv

@[expose] public section

/-!
# Function-level divergence through every call form: regression fixtures

`fdMod` validates and instantiates; its store is typed, its functions are Wasm functions with
function types, and it passes the tail-aware store check `Interp.tExt`, so the two-way function
theorems (`Function.invoke_diverges_iff_mdivT`, `Function.funDivX_iff_mdivT`) apply to every
function, at every deterministic profile `o`, with no host:

* **`fd_recursive`**: functions `0` (`call_indirect` through table `0` to itself), `1` (`call_ref`
  on global `0`, itself) and `2` (`return_call` to itself) diverge, natively (`FunDivX`), in Core
  3.0 (their invocations), and as machine frame divergence on their bodies (`MDivT`): divergence
  inside an indirect callee, a reference callee and a tail callee.
* **`fd_trap`**: functions `3` (`return_call_indirect` through table `1`'s null slot) and `4`
  (`call_ref` on null, global `1`) trap: they have a closed outcome, so none of the three holds.
  A null tail call or call by reference is a trap, never divergence.
-/

namespace Silmaril.Wasm.Cfg.ExampleFunDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge

/-- **Recursion through `call_indirect`, `call_ref` and `return_call` diverges**, at the function
level, natively, in Core 3.0 and in the machine. -/
theorem fd_recursive (o : SingleThreaded.GrowOracle) (a : Nat) (g : Func)
    (h : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2) :
    ∃ fi : FuncInst Empty, fdStore.funcs[a]? = some fi ∧ fi.code = .wasm g ∧
      FunDivX fdStore a [] ∧ Diverges (SingleThreaded.profile o) noHostX (invoke fdStore a []) ∧
      Cfg.Machine.MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel Empty))
        (Cfg.Function.calleeDivX o) g.body
        (Cfg.Machine.initial g.body fdStore (Frame.forCall fi.module [] g.locals)) := by
  have hdiv : FunDivX fdStore a [] := by
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Proofs.ExampleFunDiv.fd0_div
    · exact Proofs.ExampleFunDiv.fd1_div
    · exact Proofs.ExampleFunDiv.fd2_div
  obtain ⟨fi, hfi, hc, h1, h2⟩ := Proofs.ExampleFunDiv.fd_iff o a g (by
    rcases h with h | h | h <;> simp [h])
  exact ⟨fi, hfi, hc, hdiv, h1.1 hdiv, h2.1 hdiv⟩

/-- **Null tail calls and null calls by reference trap, and never diverge**, at the function
level, natively, in Core 3.0 and in the machine. -/
theorem fd_trap (o : SingleThreaded.GrowOracle) (a : Nat) (g : Func)
    (h : a = 3 ∧ g = g3 ∨ a = 4 ∧ g = g4) :
    ∃ fi : FuncInst Empty, fdStore.funcs[a]? = some fi ∧ fi.code = .wasm g ∧
      ClosedOutcomeX fdStore a [] fdStore .trap ∧ ¬ FunDivX fdStore a [] ∧
      ¬ Diverges (SingleThreaded.profile o) noHostX (invoke fdStore a []) ∧
      ¬ Cfg.Machine.MDivT (SingleThreaded.profile o) noHostX
        (CX (closedCallX : Abstract.CallRel Empty)) (Cfg.Function.calleeDivX o) g.body
        (Cfg.Machine.initial g.body fdStore (Frame.forCall fi.module [] g.locals)) := by
  have htrap : ClosedOutcomeX fdStore a [] fdStore .trap := by
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Proofs.ExampleFunDiv.fd3_trap
    · exact Proofs.ExampleFunDiv.fd4_trap
  have hnd := not_funDivX_of_closedOutcomeX htrap
  obtain ⟨fi, hfi, hc, h1, h2⟩ := Proofs.ExampleFunDiv.fd_iff o a g (by
    rcases h with h | h <;> simp [h])
  exact ⟨fi, hfi, hc, htrap, hnd, fun hd => hnd (h1.2 hd), fun hm => hnd (h2.2 hm)⟩

end Silmaril.Wasm.Cfg.ExampleFunDiv
