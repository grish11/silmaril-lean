module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Native
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H} {site : IndirectSite} {callee : MemoryTarget}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes written : ByteArray} {phase next : Phase H}
  {dst : Config H}

theorem ready_step (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn) (move : Edge mem host site callee bytes phase written next)
    (ready : Ready mem host site callee phase) : Ready mem host site callee next :=
  Proofs.ready_step_at linked registered move rfl ready

theorem live_step (move : Edge mem host site callee bytes phase written next) (live : mem.Live bytes) : mem.Live written :=
  Proofs.live_step move live

/-- A callee step preserves the live extent guard and the full ordered
argument and result checks for the active callee and suspended callers.
Returned host outcomes reestablish the same store representation. -/
theorem preserves (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn) (move : Edge mem host site callee bytes phase written next)
    (ready : Ready mem host site callee phase) (live : mem.Live bytes) : Ready mem host site callee next ∧ mem.Live written :=
  ⟨Proofs.ready_step_at linked registered move rfl ready, Proofs.live_step move live⟩

/-- Host-free callee steps preserve or increase the extent. -/
theorem extent_mono (move : Edge mem Execution.Runtime.noHostCalls site callee bytes phase written next) : bytes.size ≤ written.size :=
  Proofs.extent_mono move

/-- Exact native steps of the reached callee in the caller's operand and
instruction context, including direct and indirect Wasm children. The proof
uses the finite continuation stack and requires allocation links without
rank descent. Direct resolution uses the checked function index to leave a
pending invocation. Indirect lookup also consumes the live selector and can
trap with the current bytes. Both host paths share a pending phase that uses
the embedding contract to recover the returned store, with a self-step for
declared divergence. Parameterless conditionals select a source block and
enter its arm label in distinct native steps. The arm uses its own result
signature and the same live frame and store. A checked `br_if` can target
an explicit arm label or the implicit function result label. Zero consumes
only the guard. A nonzero guard leaves a pending native branch. Each
crossed label lowers the depth and skips its own suffix, keeping the live
operands for the next step. The target label
then delivers the typed payload. An explicit label resumes above its
saved operands. The function label leaves the payload inside the frame
until a separate frame exit restores the caller's saved operands and
continuation. A child's frame exit can also expose a trap for cleanup. -/
theorem step_iff (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (ready : Ready mem host site callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Step host (config mem caller saved tail callee bytes phase) dst ↔
      ∃ written next, Edge mem host site callee bytes phase written next ∧ dst = config mem caller saved tail callee written next :=
  Proofs.step_iff linked registered allocated ready live notDone

/-- After the function label delivers its ordered results, the next native
step restores the caller with its saved operands, the delivered values,
the live bytes, and one copy of the suspended continuation. -/
theorem frame_result_iff {args payload : List Value} (typed : payload.map Value.type = callee.fn.declaration.results) :
    Step host (config mem caller saved tail callee bytes (.exit args (.values payload))) dst ↔
      dst = ⟨mem.store bytes, caller, values (saved ++ payload) ++ tail⟩ :=
  Proofs.frame_result_iff typed

/-- The caller's surrounding label remains in place while the callee steps. -/
theorem stays (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out :=
  Proofs.stays notDone

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee
