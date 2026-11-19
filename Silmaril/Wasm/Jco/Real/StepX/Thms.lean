module

public import Silmaril.Wasm.Jco.Real.StepX.Defs
public import Silmaril.Wasm.Jco.Real.Step.Thms
import Silmaril.Proofs.Wasm.Jco.Real.Trap

/-!
# Adaptor code with `memory.copy`, `if` and stores against the reference engine: theorems

Proofs in `Silmaril.Proofs.Wasm.Jco.Real.{Copy,Framing,StepX,Trap}`. As in
`Silmaril.Wasm.Jco.Real.Step.Thms`, everything is over the real instance
`realInst H P host mi ma` at every profile `P` and host `host`, in a Core frame linked to it
(`FrameEnv`), and the direction is forward: returned runs of the abstract adaptor are runs of
the reference semantics. The hypotheses beyond `Step.Thms` are those of
`Silmaril.Wasm.Jco.Real.StepX.Defs`: the code is well typed (`tyExec`), the wrapped exports
return values of the declared types (`CallsTyped`), and the memory has at most `2^32` bytes
before the run (`MemOk`) and after every call of the wrapped instance (`CallsKeepMem`).

* **`execT_agree`**: a returned run of well-typed adaptor code (`memory.copy`, `if … else …
  end`, integer stores, and `Frag`'s instructions) is a reference-semantics run of its Core 3.0
  image, ending in a frame of the same module with the new locals. Core's byte-by-byte
  `memory.copy` computes the abstract `memmove`; an `if` branch runs inside its block's label on
  an empty operand stack.
* **`invokeT_agree`**: an invoked well-typed adaptor function returns exactly the values of
  `XFn.run`, in the same final store.
* `memOk_exec`: returned runs keep `MemOk`.
* `reallocShimX_typed`, **`reallocShimX_core`**: the moving `cabi_realloc` of the string-encoding
  wrappers (`reallocShimX`, used by `wrapE` for `utf16` and `latin1+utf16`: `if`, `select`,
  `memory.copy`) is well typed when `alloc` returns one `i32`, so its Core 3.0 image computes the
  emulated `realloc` `reallocEmu`: allocate, then `memmove` the old block.

* **Traps** (`execT_trap`, `invokeT_trap`, `reallocShimX_core_trap`): when, moreover, every trap
  of a call of the wrapped instance is a Core trap (`CallsTrapCore`), a trapping run of
  well-typed code is matched by a Core run that reaches `trap`. Well-typed code traps only where
  Wasm does: out-of-bounds `memory.copy`, loads and stores, and trapping calls.

Not covered: float loads and stores (outside `tyStep`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)
  {rt : String → List NumType} {lt : List NumType}

/-- **Well-typed adaptor code agrees with the reference engine.** -/
theorem execT_agree (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) {is : List XInstr} {ts ts' : List NumType}
    (hty : tyExec rt lt is ts = some ts') {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (hf : Typed lt ts f) (hok : MemOk ma s)
    (h : execX (realInst H P host mi ma) is f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    ∃ cf' : Silmaril.Wasm.Execution.Core.Frame, cf'.module = cf.module ∧
      cf'.locals = localsOf f'.locals ∧
      Steps P host ⟨s, cf, stackCode f.stack ++ codeOf fi is⟩ ⟨s', cf', stackCode f'.stack⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.sim_execT P host mi ma fi hC hK is hty hf hok h he hl

/-- Returned runs keep `MemOk`. -/
theorem memOk_exec (hK : CallsKeepMem P host mi ma) {is : List XInstr}
    {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : execX (realInst H P host mi ma) is f s (.ok f' s')) (hok : MemOk ma s) : MemOk ma s' :=
  Silmaril.Proofs.Wasm.Jco.Real.exec_memOk P host mi ma hK is h hok

/-- **An invoked well-typed adaptor function agrees with `XFn.run`.** The parameters have the
types `lt`; the extra locals are `i32` (as `XFn.toLime` declares them). -/
theorem invokeT_agree (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (fn : XFn) (ty : Nat) {rts : List NumType}
    (hty : tyExec rt (lt ++ List.replicate fn.locals tI32) fn.body [] = some rts)
    {args rs : List Flat} (ha : args.map (·.type) = lt) {s s' : Store H} (hok : MemOk ma s)
    (h : fn.run (realInst H P host mi ma) args s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : args.length = ps.length) (hrts : rs.length = rts'.length) :
    Steps P host (invoke s b (args.map toVal)) ⟨s', {}, vals (rs.map toVal)⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.invoke_xfnT P host mi ma fi hC hK fn ty hty ha hok h hb hcode he
    hexp hps hrts

/-! ## The moving `cabi_realloc` -/

/-- `reallocShimX` is well typed when `alloc` returns one `i32`. -/
theorem reallocShimX_typed (alloc : String) (hA : rt alloc = [tI32]) :
    tyExec rt ([tI32, tI32, tI32, tI32] ++ List.replicate (reallocShimX alloc).locals tI32)
      (reallocShimX alloc).body [] = some [tI32] := by
  simp [reallocShimX, tyExec, tyStep, hA]

/-- **The moving `cabi_realloc` on Core 3.0**: when `alloc` returns one `i32`, the Core 3.0
image of `reallocShimX alloc` (`if`, `select`, `memory.copy`), invoked on `i32` arguments,
returns what the emulated `realloc` `reallocEmu` returns (allocate, then copy
`min(old_size, new_size)` bytes of the old block), in the same final store. -/
theorem reallocShimX_core (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (alloc : String) (hA : rt alloc = [tI32]) (ty : Nat)
    {old os al ns : BitVec 32} {rs : List Flat} {s s' : Store H} (hok : MemOk ma s)
    (h : reallocEmu (realInst H P host mi ma) alloc old os al ns s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm ((reallocShimX alloc).toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : 4 = ps.length) (hrts : rs.length = rts'.length) :
    Steps P host (invoke s b ([Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns].map toVal))
      ⟨s', {}, vals (rs.map toVal)⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.realloc_core P host mi ma fi hC hK alloc hA
    (reallocShimX_typed alloc hA) ty hok h hb hcode he hexp hps hrts

/-! ## Traps -/

/-- **Trapping well-typed adaptor code reaches a Core trap.** -/
theorem execT_trap (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (hT : CallsTrapCore P host mi ma) {is : List XInstr}
    {ts ts' : List NumType} (hty : tyExec rt lt is ts = some ts') {f : Silmaril.Wasm.Jco.Frame}
    {s : Store H} (hf : Typed lt ts f) (hok : MemOk ma s)
    (h : execX (realInst H P host mi ma) is f s .trap)
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    ∃ s' cf', Steps P host ⟨s, cf, stackCode f.stack ++ codeOf fi is⟩ ⟨s', cf', [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.trap_execT P host mi ma fi hC hK hT is hty (st := []) hf.1 hf.2
    hok (by simpa using h) he hl

/-- **An invoked well-typed adaptor function that traps reaches a Core trap.** -/
theorem invokeT_trap (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (hT : CallsTrapCore P host mi ma) (fn : XFn) (ty : Nat)
    {rts : List NumType} (hty : tyExec rt (lt ++ List.replicate fn.locals tI32) fn.body [] = some rts)
    {args : List Flat} (ha : args.map (·.type) = lt) (hn : args.length = fn.params) {s : Store H}
    (hok : MemOk ma s) (h : fn.run (realInst H P host mi ma) args s .trap) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : args.length = ps.length) :
    ∃ s', Steps P host (invoke s b (args.map toVal)) ⟨s', {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.invoke_xfnT_trap P host mi ma fi hC hK hT fn ty hty ha hn hok h hb
    hcode he hexp hps

/-- **The moving `cabi_realloc` traps as on Core 3.0**: when `reallocEmu` traps (an
out-of-bounds copy, or a trapping `alloc`), the Core 3.0 image of `reallocShimX` reaches
`trap`. -/
theorem reallocShimX_core_trap (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (hT : CallsTrapCore P host mi ma) (alloc : String)
    (hA : rt alloc = [tI32]) (ty : Nat) {old os al ns : BitVec 32} {s : Store H}
    (hok : MemOk ma s) (h : reallocEmu (realInst H P host mi ma) alloc old os al ns s .trap)
    {b : Nat} {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm ((reallocShimX alloc).toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts')) (hps : 4 = ps.length) :
    ∃ s', Steps P host (invoke s b ([Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns].map toVal))
      ⟨s', {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.realloc_core_trap P host mi ma fi hC hK hT alloc hA
    (reallocShimX_typed alloc hA) ty hok h hb hcode he hexp hps

end Silmaril.Wasm.Jco.Real
