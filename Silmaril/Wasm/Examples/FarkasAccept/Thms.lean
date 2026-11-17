module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Sound

/-!
# The Farkas acceptor as a core Wasm module: theorems

Core 3.0 small-step execution, every numerics profile, every host relation; no determinism
assumption. Proofs in `Silmaril.Proofs.Wasm.Examples.FarkasAccept.*`.

* **The instance** (`decide +kernel`): `prog` validates and instantiates (`instance_isSome`); its
  exported functions are at the addresses `3`, `4` (`cabi_realloc`, `check`, `exportAddrs`). The
  kernel checks also give that every function of the instance has the module's code and type
  and that the module instance resolves globals, memories and functions as in the module (used
  by the proofs, `…FarkasAccept.Inst`).
* **Soundness of the check** (`check_sound`): in every store of the acceptor (`AccStore`: the
  instance's functions, **any** checker state, any heap pointer, a 1 MiB ABI memory `B₁`) with
  the records of the system in memory (`IneqsIn`) and the multipliers in memory, every run of
  `check` that returns `[r]` with `r ≠ 0` puts the system read from `B₁` (`systemAt`) in
  `Infeasible`: it has no solution over any ordered field. The multipliers need no assumption:
  the check resets the checker (its `check()`), feeds every inequality as `row`/`entry` calls,
  and the checker's invariant (`Silmaril.Wasm.Examples.Farkas.Inv`, generalised to a fixture
  with further globals and memories) makes a nonzero final `check()` certify the rows it holds,
  each an inequality of the system with its coefficients reversed.
* **The allocator** (`realloc_sound`): every returning run of `cabi_realloc` answers one value
  and only sets the heap pointer, as `ReallocOk` says (bump, never lower, blocks fresh).

Not claimed: completeness (that every valid certificate within the bounds is accepted; the
Wasmtime suite `tools/wasm-acceptor-harness/suites/farkas.json` tests it on examples),
agreement with `Carrier.farkasCheck` (outside the checker's bounds valid certificates are
rejected), termination, and anything about the component binary beyond the core module.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.LinArith.Carrier (Infeasible)

/-! ## The instance -/

theorem instance_isSome : (Silmaril.Wasm.Verify.instance? prog).isSome = true :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.acc_instance

theorem exportAddrs : accI.addrs = [3, 4] :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.acc_addrs

variable {P : Profile} {host : HostSemantics Nat}

/-! ## The check -/

/-- **Soundness of `check`**: a nonzero answer refutes the system in memory. -/
theorem check_sound {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray} (hs : AccStore s top B₁)
    {sp sl yp yl : BitVec 32} (hsp : IneqsIn B₁ sp.toNat sl.toNat)
    (hyp : yp.toNat + 8 * yl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 4 [Val.i32 sp, Val.i32 sl, Val.i32 yp, Val.i32 yl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    systemAt B₁ sp.toNat sl.toNat ∈ Infeasible :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.check_sound hs hsp hyp hrun hr

/-! ## The allocator -/

/-- **`cabi_realloc`, every returning run.** -/
theorem realloc_sound {s : Store Nat} (hf : s.funcs = accS.funcs) {top : BitVec 32}
    (hg : s.globals[4]? = some ⟨accG32, Val.i32 top⟩) (htop : top.toNat ≤ memBytes)
    {old osz al nsz : BitVec 32} {s' : Store Nat} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s 3 [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal 4 (Val.i32 t') ∧
      ReallocOk top al nsz r t' :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.realloc_sound hf hg htop hrun

end Silmaril.Wasm.Examples.FarkasAccept
