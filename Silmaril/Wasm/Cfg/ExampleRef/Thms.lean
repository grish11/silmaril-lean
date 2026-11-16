module

public import Silmaril.Wasm.Cfg.ExampleRef.Defs
public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleRef

@[expose] public section

/-!
# Calls by reference in the block-CFG machine: divergence versus trap

Regression fixtures for callee divergence through `call_ref` (`BodyCallDivRef`) and for the
separation of a null call (a trap) from divergence. Both bodies are one block with no terminator,
so the machine has **no infinite run** from either entry, for every oracle (`refBody_not_infinite`,
`nullBody_not_infinite`).

* **`ref_machine_div`**: in a frame of `Abstract.recMod`'s module, whose function `0` is the
  validated self-call `(func (call 0))` and `x` names it, `refBody x y` (`ref.func x; call_ref y`)
  reaches a call by reference of that function. `MDivC` with the checked closed oracle
  `closedCallOk` and `closedDiv` holds (through `BodyCallDivRef`), and Core 3.0 diverges on the body
  (`mdivC_core_closed`).
* **`null_machine_trap`**: `nullBody ht y` (`ref.null ht; call_ref y`) moves the machine to the
  `trap` sink in one step, in the same store and frame (every profile, host and oracle). Core
  3.0 never diverges on it (`null_not_diverges`), so `MDivC` with the closed oracle fails
  (`null_not_mdivC`).

The bodies run in the callee's module frame. They are not functions of `recMod`: the closed
oracle's store check `Interp.StoreChk` (no extension) rejects `call_ref` in function bodies, and
admits it only through an extension such as `tExt`. A `call_indirect` fixture needs a store with
a table and is not included.
-/

namespace Silmaril.Wasm.Cfg.ExampleRef

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract
  Silmaril.Wasm.Cfg.Machine

/-- **No infinite machine run from `refBody`**, for every oracle. -/
theorem refBody_not_infinite {H : Type} {P : Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} (x : FuncIdx) (y : TypeIdx) (s : Store H) (f : Frame) :
    ¬ InfiniteTrace (MStepC P host C (refBody x y)) (initial (refBody x y) s f) :=
  Proofs.ExampleRef.not_infinite (by simp [isTerminator]) (by simp [isTerminator]) s f

/-- **No infinite machine run from `nullBody`**, for every oracle. -/
theorem nullBody_not_infinite {H : Type} {P : Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} (ht : HeapType) (y : TypeIdx) (s : Store H) (f : Frame) :
    ¬ InfiniteTrace (MStepC P host C (nullBody ht y)) (initial (nullBody ht y) s f) :=
  Proofs.ExampleRef.not_infinite (by simp [isTerminator]) (by simp [isTerminator]) s f

/-- **`MDivC` at `refBody`**: in a frame where `x` names `recStore`'s self-call, the body
reaches `call_ref` of it, which `closedDiv` names. -/
theorem ref_mdivC (P : Profile) {fi : FuncInst Empty} {f : Frame} (x : FuncIdx) (y : TypeIdx)
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (refBody x y)
      (initial (refBody x y) recStore f) :=
  Proofs.ExampleRef.ref_mdivC P x y hfi hx

/-- **A call by reference of the validated self-recursive function of `recMod`** (every
profile, no host): in that function's call frame, with `x` the index its own body calls,
`refBody x y` has no infinite machine run,
`MDivC` with the checked closed oracle and `closedDiv` holds, and Core 3.0 diverges on it. -/
theorem ref_machine_div (P : Profile) (y : TypeIdx) :
    ∃ (fi : FuncInst Empty) (fn : Func) (x : FuncIdx),
      recStore.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧ fn.body = [.call x] ∧
      ¬ InfiniteTrace (MStepC P (fun _ _ _ _ => False) Abstract.closedCallOk (refBody x y))
        (initial (refBody x y) recStore (Frame.forCall fi.module [] fn.locals)) ∧
      MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (refBody x y)
        (initial (refBody x y) recStore (Frame.forCall fi.module [] fn.locals)) ∧
      Diverges P (fun _ _ _ _ => False)
        ⟨recStore, Frame.forCall fi.module [] fn.locals, expression (refBody x y)⟩ := by
  obtain ⟨fi, fn, x, ps, rs, hfi, hcode, hbody, hx, -⟩ := rec_selfLoop
  have hm := ref_mdivC P (f := Frame.forCall fi.module [] fn.locals) x y hfi hx
  exact ⟨fi, fn, x, hfi, hcode, hbody, refBody_not_infinite x y _ _, hm, mdivC_core_closed P hm⟩

/-- **The machine at `nullBody` traps in one step**, in the same store and frame. -/
theorem null_machine_trap {H : Type} {P : Profile} {host : HostSemantics H}
    {C : Abstract.CallRel H} (ht : HeapType) (y : TypeIdx) (s : Store H) (f : Frame) :
    MStepC P host C (nullBody ht y) (initial (nullBody ht y) s f) ⟨.trap, [], [], s, f⟩ :=
  Proofs.ExampleRef.null_trap ht y s f

/-- **Core 3.0 never diverges on `nullBody`** (every profile and host). -/
theorem null_not_diverges {H : Type} {P : Profile} {host : HostSemantics H} (ht : HeapType)
    (y : TypeIdx) (s : Store H) (f : Frame) :
    ¬ Diverges P host ⟨s, f, expression (nullBody ht y)⟩ :=
  Proofs.ExampleRef.null_not_div ht y s f

/-- **`MDivC` fails at `nullBody`** with the checked closed oracle: it would be Core divergence. -/
theorem null_not_mdivC (P : Profile) (ht : HeapType) (y : TypeIdx) (s : Store Empty) (f : Frame) :
    ¬ MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (nullBody ht y)
      (initial (nullBody ht y) s f) :=
  fun h => null_not_diverges ht y s f (mdivC_core_closed P h)

end Silmaril.Wasm.Cfg.ExampleRef
