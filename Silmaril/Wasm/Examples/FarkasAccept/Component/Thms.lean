module

public import Silmaril.Wasm.Examples.FarkasAccept.Component.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Logic.LinArith.Carrier.Defs
public import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.Sound
import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.Bytes

/-!
# The Farkas acceptor as a component: theorems

**Accepting calls are sound**, for the reference machine at every numerics profile `P` and
every component choice profile `prof` (namespace `Silmaril.Wasm.Examples.FarkasAccept.Component`;
the core-level theorem of the same name is `Silmaril.Wasm.Examples.FarkasAccept.check_sound`):

* `check_sound`: if calling `check` of `farkasComp.toRef` on the `list<ineq>` value of a system
  `S : SystemW` and the `list<s64>` value of multipliers `y` can return `true`, then
  `S ∈ Infeasible`: `S` has no solution over any ordered field.

The multipliers are not constrained. Only accepting behaviours are: traps, divergence and
`false` answers are not (no completeness is claimed; outside the checker's bounds valid
certificates are rejected).

The proof (`Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component`) combines

* `acceptSound farkasComp` (`Silmaril.Wasm.Component.Reference.ListLift`), whose hypotheses are
  `farkasComp_good` and `farkasComp_inst` (the instance `accI` of `prog`, by kernel evaluation;
  the ABI memory is the module's memory `1`, `farkasComp.memIdx`);
* the **memory lemma** `lowered`: the lowering of the two arguments into memory address `1`
  ends with the flat arguments `(q₁, len₁, q₂, len₂)` in a store of the acceptor (`AccStore`:
  the instance's functions, some checker state, some heap pointer, the 1 MiB ABI memory `B₁`),
  with the records of the system in memory (`IneqsIn B₁ q₁ len₁`), the system read back from
  them (`systemAt B₁ q₁ len₁ = S`: each `ineq` at `q₁ + 16 i`, its `coeffs` pair at `+0`, its
  `bound` at `+8`; each `tuple<u32, s64>` at `+0` and `+8` of its 16 bytes), and the multipliers
  `wordsAt64 B₁ q₂ len₂ = y`. It is the generic `params_holds` (`…ListLift.Bump`) for the bump
  allocator `cabi_realloc` (`farkasBump`, from `realloc_sound`, at every alignment); the
  lowering writes only memory `1` and the allocator only the heap pointer, so the store stays a
  store of the acceptor;
* the core soundness theorem `Silmaril.Wasm.Examples.FarkasAccept.check_sound`, which holds from
  any checker state.

**The bytes** (by kernel evaluation): `coreBytes` decode to `prog` (`decode_coreBytes`) and
`bytes` parse to `farkasComp.toAst coreBytes` (`bytes_parse`). That the reference reading of the
parsed component (`Silmaril.Project.WasmComponents.Ref.toRef?`) is `farkasComp.toRef` is in
`Silmaril.Project.WasmComponents.FarkasAccept.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.FarkasAccept.Component

open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.LinArith.Carrier (SystemW S64 Infeasible)

/-! ## The bytes -/

/-- **The core module bytes decode to `prog`.** -/
theorem decode_coreBytes : Silmaril.Wasm.Binary.Core.decode? coreBytes = some prog :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.decode_coreBytes

/-- **The component bytes parse to the emitted component.** -/
theorem bytes_parse :
    Silmaril.Wasm.Component.Binary.parse bytes = .ok (farkasComp.toAst coreBytes) :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.bytes_parse

/-! ## The fragment and the allocator -/

/-- `farkasComp` is well formed. -/
theorem farkasComp_good : farkasComp.Good :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.farkasComp_good

/-- `accI` is the instance of `prog` that `acceptSound` assumes, with the ABI memory at
address `1`. -/
theorem farkasComp_inst : farkasComp.Inst accI :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.farkasComp_inst

/-- **`cabi_realloc` is a bump allocator** (function address `3`, memory address `1`). -/
theorem farkasBump (P : Profile) : BumpAlloc P 3 1 memBytes FInv :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.farkasBump P

/-- The instance store meets the invariant, with the heap pointer at `heapBase`. -/
theorem fInv_init : FInv accI.store heapBase :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.fInv_init

/-! ## The memory lemma -/

/-- **The two lowered arguments in memory**: lowering the system `S` and the multipliers `y`
from the instance store, through the allocator (address `3`) into memory address `1`, ends with
the flat arguments `(q₁, len₁, q₂, len₂)` in a store of the acceptor (`AccStore`, some heap
pointer `top`, ABI memory `B₁`) whose memory holds the records of `S` (`IneqsIn`), read back as
`S` (`systemAt`), and the multipliers (`wordsAt64`). -/
theorem lowered {P : Profile} {S : SystemW} {y : List S64} {s : Store Nat}
    {fl : List Silmaril.Wasm.Execution.Core.Val}
    (hL : LParams P 3 1 [.list ineqTy, .list .s64] [ofSystem S, ofS64s y] accI.store fl s) :
    ∃ q₁ q₂ top B₁, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 S.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 y.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ S.length < 2 ^ 32 ∧ y.length < 2 ^ 32 ∧
      AccStore s top B₁ ∧ IneqsIn B₁ q₁ S.length ∧ systemAt B₁ q₁ S.length = S ∧
      q₂ + 8 * y.length ≤ B₁.size ∧ wordsAt64 B₁ q₂ y.length = y :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.lowered hL

/-! ## Soundness of accepting calls -/

/-- **An accepting call of `check` is on an infeasible system**, whatever the multipliers. -/
theorem check_sound (P : Profile) (prof : ProfileKind) (S : SystemW) (y : List S64)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) ()
      farkasComp.toRef [] "check" [(ofSystem S).toRef, (ofS64s y).toRef]) :
    S ∈ Infeasible :=
  Silmaril.Proofs.Wasm.Examples.FarkasAccept.Component.check_sound P prof S y h

end Silmaril.Wasm.Examples.FarkasAccept.Component
