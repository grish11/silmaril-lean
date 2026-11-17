module

public import Silmaril.Wasm.Cfg.MachineLDiv.Defs
public import Silmaril.Wasm.Abstract.XDivergeP.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLDivF

@[expose] public section

/-!
# Quiescent divergence of the logged block-CFG machine (H2, theorems)

Host-free divergence of a body, natively, is `XDivergeP.EvalDivXP`: the coinductive divergence of
the closed native semantics `EvalOXP closedCallXP`, with finite parts answered by the closed oracle.
On the machine it is `MDivL` (infinite oracle-answered local steps `InfK`, or a diverging callee
`CalleeDivK`), and at a call's frame `FunDivL`, which adds the diverging tail callee `TailDivK`
(`MachineLDiv.Defs`).

* **`div_machine`** (native to machine): native divergence of a body from the empty stack is
  machine divergence from the CFG entry. Divergence inside a callee is the machine's
  `CalleeDivK`, at the block making the call. Divergence of the body's own code, through blocks,
  loops (re-entered by branches, caught exceptions included), conditionals and handlers, is
  `InfK`, an infinite run of the machine.
* **`calleeDiv_div`** (machine to native, the callee form): a diverging callee reached from the
  CFG entry is native divergence of the body.
* **`funDiv_machine`**: native frame divergence of a call (`FunDivXP`: the body diverges, or it
  ends in a pending tail call whose callee diverges) is `FunDivL`.
* **`funDiv_of_calleeDiv`, `funDiv_of_tailDiv`**: the converse for the callee and tail-callee forms.

Not yet here: the converse for infinite local steps (`InfK` from the CFG entry is native
divergence of the body), hence `MDivL`, `FunDivL` and native divergence as equivalences;
divergence after a host-event log (`LogDivXP`); productive streams. The closed answers and the
diverging callees are those of the native oracle: this does not discharge H3
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

end Silmaril.Wasm.Cfg.MachineL
