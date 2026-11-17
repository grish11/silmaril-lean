module

public import Silmaril.Wasm.Acceptor.Alloc.Defs
public import Silmaril.Wasm.Execution.Core.Step
import Silmaril.Proofs.Wasm.Acceptor.Alloc

/-!
# The acceptor kit: the bump allocator `cabi_realloc`, results

Core 3.0 small-step execution, every numerics profile, every host relation. Proofs in
`Silmaril.Proofs.Wasm.Acceptor.Alloc`.

* **`realloc_sound`**: every returning run of `$invoke` of a function instance with the code
  `reallocFunc ty g N`, whose module instance maps global `g` to the address `ga` holding the
  `i32` heap pointer `top ≤ N`, answers one value `r` and only sets that global, to some `t'`, as
  `ReallocOk N top al nsz r t'` says.
* **`BumpSpec.bumpAlloc`**: an allocator meeting `BumpSpec` is a `ListLift.BumpAlloc` for any
  memory whose size is `N` under the invariant and whose writes keep it; so `params_holds`
  applies to every component built on it.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Reference.ListLift (BumpAlloc memBytesOf)

/-- **`cabi_realloc`, every returning run.** -/
theorem realloc_sound {H : Type} {P : Profile} {host : HostSemantics H} {g ga N : Nat}
    {gt : CGlobalType} {top : BitVec 32} {s : Store H} {a : Nat} {fi : FuncInst H}
    {ty : TypeIdx} {ps rs : Ty (.list .val)} (hN : N < 2 ^ 32) (hg : g < 2 ^ 32)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm (reallocFunc ty g N))
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 4) (hrs : rs.length = 1)
    (hmi : fi.module.globals[g]? = some ga) (hgl : s.globals[ga]? = some ⟨gt, Val.i32 top⟩)
    (htop : top.toNat ≤ N)
    {old osz al nsz : BitVec 32} {s' : Store H} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s a [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal ga (Val.i32 t') ∧
      ReallocOk N top al nsz r t' :=
  Silmaril.Proofs.Wasm.Acceptor.realloc_sound hN hg hfi hcode he hps hrs hmi hgl htop hrun

/-- **A bump allocator on a global is a `BumpAlloc`.** -/
theorem BumpSpec.bumpAlloc {P : Profile} {ra ga ma N : Nat} {Inv : Store Nat → Nat → Prop}
    (hS : BumpSpec P ra ga N Inv) (size : ∀ {s t}, Inv s t → (memBytesOf s ma).size = N)
    (write : ∀ {s t p bs s'}, Inv s t →
      Silmaril.Wasm.SingleThreaded.memWrite? s ma p bs = some s' → Inv s' t) :
    BumpAlloc P ra ma N Inv :=
  Silmaril.Proofs.Wasm.Acceptor.BumpSpec.bumpAlloc hS size write

end Silmaril.Wasm.Acceptor
