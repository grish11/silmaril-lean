module

public import Silmaril.Wasm.Cfg.MachineL.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd

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

* **`backward`** (H2, the converse, finished outcomes): an `EvalLXPS` run of the body from the
  empty stack, to any outcome but a branch past the function label, is a logged run from the CFG
  entry to an end standing for it, with **exactly** the native log split between the run and the
  end: a sink (`EndRel`), or a block whose straight-line code makes the pending tail call
  (`TailL`). The proof is a continuation-passing induction on the native derivation. Each
  derivation's motive takes, as a hypothesis, what the machine does once its sequence ends
  (`ExitE`), and a loop's re-run by `loopBack` starts from the entry of its arm, where re-entering
  the loop lands.

A branch past the function label (`brk (k + 1)` at the body's top level) has no machine end: the
machine does not step there, and no behaviour of the open module (`wasmHOpenXPS`, through
`exitFlow`) comes from it.

Not yet here: pending calls (`ReachLXPS`), divergence (quiescent: infinite local steps, or a
finite run into a diverging callee) and coherent productive streams, each against the machine;
the typed projection to `MStepC`; the recursive closure (H3).

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

/-- **Native runs of the body are logged machine runs** (finished outcomes): from the CFG entry to
an end standing for the native result, with exactly the native log. -/
theorem backward {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f [] (liftInstrs body) l r)
    (hr : ∀ k ws, r.2.2 ≠ .flow (.brk (k + 1) ws)) :
    ∃ (st : MState H) (l₁ l₂ : List (SCall H)), MRunL body (initial body s f) l₁ st ∧
      l = l₁ ++ l₂ ∧ ((st.node.IsSink ∧ l₂ = [] ∧ EndRel st r) ∨ TailL body st l₂ r) :=
  Proofs.MachineLBwd.backward h hr

end Silmaril.Wasm.Cfg.MachineL
