module

public import Silmaril.Wasm.Cfg.ExampleTail.Defs
public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleTail

@[expose] public section

/-!
# Divergence through a tail callee: a regression fixture

`tailBody x` is `block (return_call x); unreachable`. In the call frame of `Abstract.recMod`'s
validated self-call `(func (call 0))`, with `x` the index its own body calls:

* **`tail_machine_div`**: the machine with the checked closed oracle enters the block and reaches
  its terminator `return_call x`, a tail call of the self-call, which `closedDiv` names, so
  `MDivT` holds (`TailCallDiv`). The function's frame `FRAME_n{fi} (LABEL_n{} body)` diverges in
  Core 3.0, in any outer frame (`mdivT_frame_closed`).

The tail call replaces the frame, so the `unreachable` after the block never runs (it would trap).
Only frame divergence is stated: the body alone, outside its frame, is stuck at the pending tail
call.
-/

namespace Silmaril.Wasm.Cfg.ExampleTail

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract
  Silmaril.Wasm.Cfg.Machine

/-- **`MDivT` at the entry of `tailBody`**, in a frame where `x` names `recStore`'s self-call. -/
theorem tail_mdivT (P : Profile) {fi : FuncInst Empty} {x : FuncIdx} {f : Frame}
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivT P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (tailBody x)
      (initial (tailBody x) recStore f) :=
  Proofs.ExampleTail.tail_mdivT P hfi hx

/-- **A tail call of the validated self-recursive function of `recMod`** (every profile, no
host): in that function's call frame, `MDivT` holds at `tailBody x`, and the frame
`FRAME_n{fi} (LABEL_n{} (block (return_call x); unreachable))` diverges in Core 3.0 in every
outer frame. -/
theorem tail_machine_div (P : Profile) :
    ∃ (fi : FuncInst Empty) (fn : Func) (x : FuncIdx),
      recStore.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧ fn.body = [.call x] ∧
      MDivT P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (tailBody x)
        (initial (tailBody x) recStore (Frame.forCall fi.module [] fn.locals)) ∧
      ∀ (n : Nat) (f : Frame), Diverges P (fun _ _ _ _ => False)
        ⟨recStore, f, [.frame n (Frame.forCall fi.module [] fn.locals)
          [.label n [] (expression (tailBody x))]]⟩ := by
  obtain ⟨fi, fn, x, ps, rs, hfi, hcode, hbody, hx, -⟩ := rec_selfLoop
  have hm := tail_mdivT P (f := Frame.forCall fi.module [] fn.locals) hfi hx
  exact ⟨fi, fn, x, hfi, hcode, hbody, hm, fun n f => mdivT_frame_closed P hm n f⟩

end Silmaril.Wasm.Cfg.ExampleTail
