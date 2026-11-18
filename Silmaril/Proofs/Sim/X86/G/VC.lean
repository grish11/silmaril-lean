module

public import Silmaril.Proofs.Sim.X86.G.Prog
public import Silmaril.Wasm.Logic.VC.Thms

/-!
# The G simulator and the verification-condition generator

`wpc` (`Silmaril.Wasm.Logic.VC`) evaluates straight-line code with `exec1`; with the simulator's
evaluation lemmas (`exec1_gget`, `exec1_gset`, ...) and the global-update lemma `gval_upd` it
evaluates generated code over a **symbolic** store. The stock `wat_vc` cannot: its `simp` set
reads globals through `Store.global?` and knows nothing about a `global.set` at one address
leaving the globals at other addresses unchanged (that needs `Layout`).

* `ctl_gget` … `ctl_b64op`: the generator treats the generated instructions as plain;
* `hwp_of_wpc`: the generator's condition for a whole code from the empty stack;
* the tactic `g_vc` (in the header `Silmaril.Sim.X86.G.Thms`) evaluates such a condition.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC (wpc ctl Invs)
open Silmaril.Wasm.Logic.Core (Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem ctl_gget (l : Loc) : ctl (gget l) = .plain := rfl
theorem ctl_gset (l : Loc) : ctl (gset l) = .plain := rfl
theorem ctl_c64 (c : BitVec 64) : ctl (c64 c) = .plain := rfl
theorem ctl_b64op (op : IntBinOp) : ctl (b64op op) = .plain := rfl

/-- The generator's condition from the empty stack gives the every-run weakest precondition of
the code. -/
theorem hwp_of_wpc {is : List Instr} {Q : Post H} {s : Store H} {f : Frame} (inv : Invs H)
    (h : wpc inv 0 is Q s f []) : Silmaril.Wasm.Logic.Hoare.HWP P host s f (expression is) Q := by
  simpa [vals] using Silmaril.Wasm.Logic.VC.wpc_sound (P := P) (host := host) inv 0 is Q s f [] h

end Silmaril.Sim.X86.G
