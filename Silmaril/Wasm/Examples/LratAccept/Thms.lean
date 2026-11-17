module

public import Silmaril.Wasm.Examples.LratAccept.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Proofs.Wasm.Examples.LratAccept.Sound

/-!
# The LRAT UNSAT acceptor as a core Wasm module: theorems

Core 3.0 small-step execution, every numerics profile, every host relation; no determinism
assumption. Proofs in `Silmaril.Proofs.Wasm.Examples.LratAccept.*`.

* **The instance** (`decide +kernel`): `prog` validates and instantiates (`instance_isSome`); its
  exported functions are at the addresses `10`, `11`, `12` (`cabi_realloc`, `check-stream`,
  `check-nested`, `exportAddrs`). The kernel checks also give that every function of the
  instance has the module's code and type and that the module instance resolves globals,
  memories and functions as in the module (used by the proofs, `…LratAccept.Inst`).
* **Soundness of the checks** (`checkStream_sound`, `checkNested_sound`): in every store of the
  acceptor (`AccStore`: the instance's functions, **any** LRAT state, any heap pointer, a 1 MiB
  ABI memory `B₁`) with the arguments in bounds, every run of `check-stream` (`check-nested`)
  that returns `[r]` with `r ≠ 0` puts the problem read from `B₁` in `UnsatStream`
  (`UnsatNested`). The certificate needs no assumption: the checks reset the LRAT state, feed
  the problem through `add_lit`/`end_clause`, and whatever certificate words follow, the LRAT
  functions keep the checker's invariant (`Silmaril.Wasm.Examples.LRAT.Good`), so `unsat()`'s
  answer is sound.
* **The allocator** (`realloc_sound`): every returning run of `cabi_realloc` answers one value
  and only sets the heap pointer, as `ReallocOk` says (bump, never lower, blocks fresh).

Not claimed: completeness (that every valid LRAT certificate is accepted), agreement with the
reference acceptors `lratStream`/`lratNested` (they differ on problems with an empty input
clause: the acceptor needs no empty-clause step there), termination, and anything about the
component binary beyond the core module.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.SAT.Carrier

/-! ## The instance -/

theorem instance_isSome : (Silmaril.Wasm.Verify.instance? prog).isSome = true :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.acc_instance

theorem exportAddrs : accI.addrs = [10, 11, 12] :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.acc_addrs

variable {P : Profile} {host : HostSemantics Nat}

/-! ## The checks -/

/-- **Soundness of `check-stream`.** -/
theorem checkStream_sound {s : Store Nat} {G : List (BitVec 32)} {B₀ B₁ : ByteArray}
    {top : BitVec 32} (hs : AccStore s G B₀ top B₁) {pp pl cp cl : BitVec 32}
    (hpp : pp.toNat + 4 * pl.toNat ≤ memBytes) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 11 [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    wordsAt B₁ pp.toNat pl.toNat ∈ UnsatStream :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.checkStream_sound hs hpp hcp hrun hr

/-- **Soundness of `check-nested`.** -/
theorem checkNested_sound {s : Store Nat} {G : List (BitVec 32)} {B₀ B₁ : ByteArray}
    {top : BitVec 32} (hs : AccStore s G B₀ top B₁) {pp pl cp cl : BitVec 32}
    (hpp : NestedIn B₁ pp.toNat pl.toNat) (hcp : cp.toNat + 4 * cl.toNat ≤ memBytes)
    {s' : Store Nat} {f' : Frame} {r : BitVec 32}
    (hrun : Steps P host (invoke s 12 [Val.i32 pp, Val.i32 pl, Val.i32 cp, Val.i32 cl])
      ⟨s', f', vals [Val.i32 r]⟩) (hr : r ≠ 0#32) :
    nestedAt B₁ pp.toNat pl.toNat ∈ UnsatNested :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.checkNested_sound hs hpp hcp hrun hr

/-! ## The allocator -/

/-- **`cabi_realloc`, every returning run.** -/
theorem realloc_sound {s : Store Nat} (hf : s.funcs = accS.funcs) {top : BitVec 32}
    (hg : s.globals[8]? = some ⟨accGt, Val.i32 top⟩) (htop : top.toNat ≤ memBytes)
    {old osz al nsz : BitVec 32} {s' : Store Nat} {f' : Frame} {res : List Val}
    (hrun : Steps P host (invoke s 10 [Val.i32 old, Val.i32 osz, Val.i32 al, Val.i32 nsz])
      ⟨s', f', vals res⟩) :
    ∃ r t' : BitVec 32, res = [Val.i32 r] ∧ s' = s.setGlobal 8 (Val.i32 t') ∧
      ReallocOk top al nsz r t' :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.realloc_sound hf hg htop hrun

end Silmaril.Wasm.Examples.LratAccept
