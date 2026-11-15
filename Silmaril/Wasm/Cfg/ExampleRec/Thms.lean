module

public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleRec

@[expose] public section

/-!
# `(func (call 0))` in the block-CFG machine: divergence inside a single callee

`recMod`, `(module (type (func)) (func (type 0) (call 0)))`, validates and instantiates
(`Abstract.rec_instantiate`); its function's body is one direct self-call. For that body, with
calls answered by the checked closed oracle `closedCallOk`:

* **`selfCall_not_infinite`**: the machine with calls has **no infinite run** from the CFG entry,
  for every oracle. The body is one block with no terminator; every step from it goes to a sink.
  An oracle answers terminating calls only, so it has no answer for the self-call at all.
* **`rec_machine_div`**: yet Core 3.0 **diverges** on the body (at every profile, in the
  function's own call frame), and machine divergence `MDivC` with `closedDiv` holds: the block's
  body reaches the self-call, which has no closed-oracle entry. This is the divergence inside a
  single callee that `MDivC`'s second disjunct (`BodyCallDiv`) adds to infinite `MStepC` runs.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract

/-- **A self-call body has no infinite machine run**, with any oracle: the body `[call x]` is
one block with no terminator, and every machine step from it goes to a sink. -/
theorem selfCall_not_infinite {H : Type} {P : Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} (x : FuncIdx) (s : Store H) (f : Frame) :
    ¬ InfiniteTrace (MStepC P host C [Instr.call x]) (initial [Instr.call x] s f) :=
  Proofs.ExampleRec.not_infinite x s f

/-- **`MDivC` at the self-call of `recMod`**: in a frame whose `call x` resolves to the function
itself, the body `[call x]` reaches a call that `closedDiv` names. -/
theorem rec_mdivC (P : Profile) {fi : FuncInst Empty} {x : FuncIdx} {f : Frame}
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv [Instr.call x]
      (initial [Instr.call x] recStore f) :=
  Proofs.ExampleRec.rec_mdivC P hfi hx

/-- **The validated self-recursive function of `recMod`, in the block-CFG machine** (every
profile, no host): its body is a direct self-call `[call x]`; in its call frame, the machine with
the checked closed oracle has no infinite run, `MDivC` with `closedDiv` holds, and Core 3.0
diverges on the body. -/
theorem rec_machine_div (P : Profile) :
    ∃ (fi : FuncInst Empty) (fn : Func) (x : FuncIdx),
      recStore.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧ fn.body = [.call x] ∧
      ¬ InfiniteTrace (MStepC P (fun _ _ _ _ => False) Abstract.closedCallOk fn.body)
        (initial fn.body recStore (Frame.forCall fi.module [] fn.locals)) ∧
      MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv fn.body
        (initial fn.body recStore (Frame.forCall fi.module [] fn.locals)) ∧
      Diverges P (fun _ _ _ _ => False)
        ⟨recStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩ := by
  obtain ⟨fi, fn, x, ps, rs, hfi, hcode, hbody, hx, -⟩ := rec_selfLoop
  have hm := rec_mdivC P (f := Frame.forCall fi.module [] fn.locals) hfi hx
  refine ⟨fi, fn, x, hfi, hcode, hbody, ?_, ?_, ?_⟩
  · rw [hbody]; exact selfCall_not_infinite x _ _
  · rw [hbody]; exact hm
  · rw [hbody]; exact mdivC_core_closed P hm

end Silmaril.Wasm.Cfg.Machine
