module

public import Silmaril.Wasm.Cfg.MachineLDiv.Defs
public import Silmaril.Wasm.Abstract.XDivergeP.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLDivF
import Silmaril.Proofs.Wasm.Cfg.MachineLDivI

@[expose] public section

/-!
# Quiescent divergence of the logged block-CFG machine (H2, theorems)

Host-free divergence of a body, natively, is `XDivergeP.EvalDivXP`: the coinductive divergence of
the closed native semantics `EvalOXP closedCallXP`, with finite parts answered by the closed oracle.
On the machine it is `MDivL` (infinite oracle-answered local steps `InfK`, or a diverging callee
`CalleeDivK`), and at a call's frame `FunDivL`, which adds the diverging tail callee `TailDivK`
(`MachineLDiv.Defs`).

* **`div_iff`**: native divergence of a body from the empty stack is exactly machine divergence
  from the CFG entry.
  * Native to machine (`div_machine`). Divergence inside a callee is the machine's `CalleeDivK`,
    at the block making the call. Divergence of the body's own code, through blocks, loops
    (re-entered by branches, caught exceptions included), conditionals and handlers, is `InfK`,
    an infinite run of the machine.
  * Machine to native: `calleeDiv_div` for a diverging callee; `infK_div` for infinite local
    steps. The run never leaves a sequence, or leaves it at a first step: the arm then ran natively
    to that step, and its outcome continues the enclosing sequence or re-enters its loop.
* **`funDiv_iff`**: native frame divergence of a call (`FunDivXP`: the body diverges, or it ends
  in a pending tail call whose callee diverges) is exactly `FunDivL` (`funDiv_machine`,
  `funDiv_of_calleeDiv`, `funDiv_of_tailDiv`, `funDiv_of_infK`).

The three forms stay distinct: `InfK` runs forever by finitely answered steps, `CalleeDivK` stops
at a call whose callee diverges, `TailDivK` stops at a pending tail call whose callee diverges.

Not yet here: divergence after a host-event log (`LogDivXP`), and productive streams. The closed
answers and the diverging callees are those of the native oracle: this does not discharge H3
(`docs/projects/wasm-cfg.md`).
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP funDivXP_iff)

variable {H : Type}

/-- **Native host-free divergence of a body is machine divergence** from the CFG entry. -/
theorem div_machine {body : Expr} {s : Store H} {f : Frame}
    (h : EvalDivXP s f [] (liftInstrs body)) : MDivL body (initial body s f) :=
  Proofs.MachineLDivB.div_machine h

/-- **A diverging callee reached from the CFG entry is native divergence of the body.** -/
theorem calleeDiv_div {body : Expr} {s : Store H} {f : Frame}
    (h : CalleeDivK body (initial body s f)) : EvalDivXP s f [] (liftInstrs body) :=
  Proofs.MachineLDivF.calleeDiv_div h

/-- **Infinite local steps from the CFG entry are native divergence of the body.** -/
theorem infK_div {body : Expr} {s : Store H} {f : Frame} (h : InfK body (initial body s f)) :
    EvalDivXP s f [] (liftInstrs body) :=
  Proofs.MachineLDivI.infK_div h

/-- **Native host-free divergence of a body is machine divergence**, both ways. -/
theorem div_iff {body : Expr} {s : Store H} {f : Frame} :
    EvalDivXP s f [] (liftInstrs body) ↔ MDivL body (initial body s f) :=
  ⟨div_machine, fun h => h.elim infK_div calleeDiv_div⟩

/-- **Native frame divergence of a call is machine frame divergence.** -/
theorem funDiv_machine {s : Store H} {a : Nat} {args : List Val} (h : FunDivXP s a args) :
    FunDivL s a args := by
  obtain ⟨fi, fn, hfi, hcode, hb | ⟨s₁, f₂, a', args', n, hrun, hY⟩⟩ := funDivXP_iff.1 h
  · exact ⟨fi, fn, hfi, hcode, .inl (div_machine hb)⟩
  · obtain ⟨st, l, hr, hT, hl⟩ := Proofs.MachineLDivF.tail_tailL hrun
    exact ⟨fi, fn, hfi, hcode, .inr ⟨st, l, s₁, f₂, a', n, args', hr, hT, hl, hY⟩⟩

/-- **A call whose body reaches a diverging callee diverges at the frame.** -/
theorem funDiv_of_calleeDiv {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H}
    {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : CalleeDivK fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals))) :
    FunDivXP s a args :=
  funDivXP_iff.2 ⟨fi, fn, hfi, hcode, .inl (calleeDiv_div h)⟩

/-- **A call whose body reaches a diverging tail callee diverges at the frame.** -/
theorem funDiv_of_tailDiv {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H}
    {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : TailDivK fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals))) :
    FunDivXP s a args :=
  funDivXP_iff.2 ⟨fi, fn, hfi, hcode, .inr (Proofs.MachineLDivF.tailDiv_tail h)⟩

/-- **A call whose body runs forever by local steps diverges at the frame.** -/
theorem funDiv_of_infK {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H}
    {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : InfK fn.body (initial fn.body s (Frame.forCall fi.module args fn.locals))) :
    FunDivXP s a args :=
  funDivXP_iff.2 ⟨fi, fn, hfi, hcode, .inl (infK_div h)⟩

/-- **Native frame divergence of a call is machine frame divergence**, both ways. -/
theorem funDiv_iff {s : Store H} {a : Nat} {args : List Val} :
    FunDivXP s a args ↔ FunDivL s a args := by
  refine ⟨funDiv_machine, ?_⟩
  rintro ⟨fi, fn, hfi, hcode, (hI | hC) | hT⟩
  · exact funDiv_of_infK hfi hcode hI
  · exact funDiv_of_calleeDiv hfi hcode hC
  · exact funDiv_of_tailDiv hfi hcode hT

end Silmaril.Wasm.Cfg.MachineL
