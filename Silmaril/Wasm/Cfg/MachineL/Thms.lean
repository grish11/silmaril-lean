module

public import Silmaril.Wasm.Cfg.MachineL.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd

@[expose] public section

/-!
# The logged block-CFG machine against the logged relation (H1)

CHECKED (standard axioms), for **all code** (no typing hypothesis): the logged machine's runs
are runs of the canonical store-retaining logged relation `Abstract.EvalLXPS` on the function
body, with **exactly** the same log of open calls, the same final store and frame.

* **`forward_sink`**: a logged run (`MRunL`) from the CFG entry (`initial`) to a sink is an
  `EvalLXPS` run of `liftInstrs body` from the empty stack, with the run's log, to a result the
  sink stands for (`EndRel`):
  * at `exit`, a flow returning the exit stack (top first): falling off the body, `return`, or a
    branch to the function label;
  * at `trap`, a trap in exactly the machine's store (a callee trap keeps the store it left);
  * at `raise`, the uncaught exception on the stack.
* **`forward_tail`**: a logged run to a block whose straight-line code ends in a pending tail
  call (`TailL`) is an `EvalLXPS` run of the body to that pending tail call, which bypasses every
  label and handler, with the logs concatenated.

The proof carries an invariant along the run backwards: at each block the rest of its sequence
runs natively, and the native rule of every enclosing structured instruction (`blockOk`,
`loopBack`, `ifOk`, `tryCatch`, `tryRethrow`, the escape rules, …) carries the outcome out of its
frame to the body's result.

**Conventions.** `MStepL` uses `EvalLXPS`'s native stack conventions at frame boundaries (see
`Silmaril.Wasm.Cfg.MachineL`), so these statements are exact without typing. They say nothing
about `Cfg.Machine.MStepC`, which uses Core's conventions: the projection to `MStepC` on typed
code is separate work, as are the converse (H2: every native run is a logged machine run), pending
calls, divergence and productive streams, and the recursive closure (H3); see
`docs/projects/wasm-cfg.md`.
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **Logged machine runs to a sink are native logged runs of the body**, with exactly their log
and store. -/
theorem forward_sink {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    {st : MState H} (h : MRunL body (initial body s f) l st) (hs : st.node.IsSink) :
    ∃ r, EvalLXPS s f [] (liftInstrs body) l r ∧ EndRel st r :=
  Proofs.MachineLFwd.forward_sink h hs

/-- **Logged machine runs to a pending tail call are native logged runs of the body to it.** -/
theorem forward_tail {body : Expr} {s : Store H} {f : Frame} {l l' : List (SCall H)}
    {st : MState H} {r : Store H × Frame × POut} (h : MRunL body (initial body s f) l st)
    (ht : TailL body st l' r) : EvalLXPS s f [] (liftInstrs body) (l ++ l') r :=
  Proofs.MachineLFwd.forward_tail h ht

end Silmaril.Wasm.Cfg.MachineL
