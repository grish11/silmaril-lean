module

public import Silmaril.Wasm.Cfg.Machine.Defs
import Silmaril.Proofs.Wasm.Cfg.Machine

@[expose] public section

/-!
# The block-CFG machine follows the extracted CFG

* `mstep_from_block`: the machine steps only from block nodes; `exit`, `trap` and `raise` are
  sinks.
* **`mstep_edge`**: every step from block `b` goes to a `Cfg.Edge` successor of `b`
  (`succOf`), or to `trap` because the block's straight-line body trapped (an instruction effect,
  `bodyTrap`).

These are graph facts, true by construction of `MStep` from `entry`/`labels`/`resolveT`.
Adequacy of the machine for `Region.Run` and Core 3.0 is the next obligation, not claimed here.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

theorem mstep_from_block {st st' : MState H} (h : MStep P host body st st') :
    ∃ b, st.node = .block b :=
  Proofs.Machine.mstep_from_block h

/-- **Every machine step follows an edge of the extracted block CFG**, or is a trap of the
block's body. -/
theorem mstep_edge {st st' : MState H} (h : MStep P host body st st') {b : BlockId}
    (hn : st.node = .block b) : Edge body b st'.node ∨ st'.node = .trap :=
  Proofs.Machine.mstep_edge h hn

end Silmaril.Wasm.Cfg.Machine
