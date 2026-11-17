module

public import Silmaril.Wasm.Cfg.MachineL.Defs
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
import Silmaril.Proofs.Wasm.Cfg.MachineLPend
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed

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

* **`backward`** (H2, the converse, finished outcomes). Hypotheses: an `EvalLXPS` run of the
  body from the empty stack to `r`, where `r` is not `brk (k + 1) ws` for any `k`, `ws`. So `r` is
  a fall-through, a `return`, `brk 0` (a branch to the function label), a trap, an uncaught
  exception, or a pending tail call. Conclusion: a logged run from the CFG entry to an end
  standing for `r`, with **exactly** the native log split between the run and the
  end: a sink (`EndRel`), or a block whose straight-line code makes the pending tail call
  (`TailL`). The proof is a continuation-passing induction on the native derivation. Each
  derivation's motive takes, as a hypothesis, what the machine does once its sequence ends
  (`ExitE`), and a loop's re-run by `loopBack` starts from the entry of its arm, where re-entering
  the loop lands.

**The excluded outcome class.** The native relation may end a body in `brk (k + 1) ws` (a branch
past the function label; invalid code can produce one). `backward` makes no claim for it:

* the logged machine has no end for it, since `DispL` has no rule for such a branch and the
  machine does not step;
* it has no *framed finished* counterpart either, since `exitFlow` gives `none` on it, so
  `wasmHOpenXPS` (and so the function closure) has no finished behaviour of the function from it.

The native body-level outcome itself does exist; only the framed function-level behaviour is
absent.

* **`pending_iff`** (H2, pending calls, both directions): the body reaches the internal call `z`
  (callee, arguments, store at the call) after the native log `l` (`ReachLXPS`) exactly when the
  logged machine runs from the CFG entry with a prefix `l₁` of `l` to a block whose straight-line
  code (or segment body) reaches `z` after the rest `l₂` (`ReachL`). The question, its pre-call
  store and the exact prefix log are those of the native reach.

  **Encoding (internal witness only).** The proof answers the pending call with a callee trap,
  which `EvalLXPS`'s `callTrap`/`indTrap`/`refTrap` record and which ends the caller at once,
  outside every handler. It then uses the finished correspondence:
  * `reach_trap`: for every trap store `s₂`, some frame;
  * `trap_reach`: the converse;
  * `trap_last`: a trap-answered entry is always last, and the run then traps in its store.
  The synthetic answer is not a claim about a real trapped session or a legal host answer; the
  theorem states only the pending question and prefix. Pending *tail* calls are not pending
  internal calls: they are ends of the body (`TailL`, `forward_tail`), made at the frame.

* **`closed_iff_logged`** (H2 divergence support): a run of the closed canonical semantics
  `EvalOXP C` is exactly an `EvalLXPS` run whose every logged call is a `C`-answer
  (`CloseOk C`).
  * Values: the callee's top `rs` results, `rs` its result types, as `EvalOXP`'s `callOk` keeps
    them.
  * Exceptions and traps: `C`'s, each with the store `C` leaves.
  * Host calls are never `C`-answers.
  Used with `C = closedCallXP` for the host-free part of divergence.

Divergence is in `Silmaril.Wasm.Cfg.MachineLDiv`. Not yet here: coherent productive streams; the
typed projection to `MStepC`; the recursive closure (H3).

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

/-- **Native runs of the body are logged machine runs** (finished outcomes): a native run to any
outcome other than `brk (k + 1) ws` (a branch past the function label, which has no framed finished
counterpart) is a logged run from the CFG entry to an end standing for the native result, with
exactly the native log. -/
theorem backward {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    {r : Store H × Frame × POut} (h : EvalLXPS s f [] (liftInstrs body) l r)
    (hr : ∀ k ws, r.2.2 ≠ .flow (.brk (k + 1) ws)) :
    ∃ (st : MState H) (l₁ l₂ : List (SCall H)), MRunL body (initial body s f) l₁ st ∧
      l = l₁ ++ l₂ ∧ ((st.node.IsSink ∧ l₂ = [] ∧ EndRel st r) ∨ TailL body st l₂ r) :=
  Proofs.MachineLBwd.backward h hr

/-- **Pending calls correspond**: the body reaches the internal call `z` after `l` exactly when the
logged machine runs to a block reaching `z`, the logs splitting `l`. -/
theorem pending_iff {body : Expr} {s : Store H} {f : Frame} {l : List (SCall H)}
    {z : (Abstract.wasmOShape H).self.Op} :
    Abstract.ReachLXPS s f [] (liftInstrs body) l z ↔
      ∃ (st : MState H) (l₁ l₂ : List (SCall H)), MRunL body (initial body s f) l₁ st ∧
        ReachL body st l₂ z ∧ l = l₁ ++ l₂ :=
  Proofs.MachineLPend.pending_iff

/-- **Closed runs are the logged runs answered by the call relation.** -/
theorem closed_iff_logged {C : Abstract.CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} :
    Abstract.CallXP.EvalOXP C s f stk es r ↔
      ∃ l, EvalLXPS s f stk es l r ∧ ∀ e ∈ l, CloseOk C e :=
  ⟨Proofs.MachineLClosed.closed_logged,
    fun ⟨_, h, hl⟩ => Proofs.MachineLClosed.logged_closed h hl⟩

end Silmaril.Wasm.Cfg.MachineL
