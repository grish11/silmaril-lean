module

public import Silmaril.Wasm.Examples.LratAccept.Component.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Proofs.Wasm.Examples.LratAccept.Component.Sound
import Silmaril.Proofs.Wasm.Examples.LratAccept.Component.Bytes

/-!
# The LRAT UNSAT acceptor as a component: theorems

**Accepting calls are sound**, for the reference machine at every numerics profile `P` and
every component choice profile `prof` (namespace `Silmaril.Wasm.Examples.LratAccept.Component`;
the core-level theorems of the same names are `Silmaril.Wasm.Examples.LratAccept.checkStream_sound`
and `checkNested_sound`):

* `checkStream_sound`: if calling `check-stream` of `lratComp.toRef` on the `list<s32>` values
  of the words `xs` and `cs` can return `true`, then `xs ∈ UnsatStream`;
* `checkNested_sound`: if calling `check-nested` on the `list<list<s32>>` value of `p` and the
  certificate words `cs` can return `true`, then `p ∈ UnsatNested`.

The certificate is not constrained. Only accepting behaviours are: traps, divergence and `false`
answers are not (no completeness is claimed).

The proof (`Silmaril.Proofs.Wasm.Examples.LratAccept.Component`) is an instance of the acceptor
kit (`Silmaril.Wasm.Acceptor`, `docs/projects/acceptor-kit.md`): the kit's
`CheckerExport.sound` applied to the kit of `lratComp` and the Core obligation of each export.
It combines

* `acceptSound lratComp` (`Silmaril.Wasm.Component.Reference.ListLift`), whose hypotheses are
  `lratComp_good` and `lratComp_inst` (the instance `accI` of `prog`, by kernel evaluation; the
  ABI memory is the module's memory `1`, `lratComp.memIdx`);
* the **memory lemma** `lowered`: the lowering of the two arguments into memory address `1` ends
  with the flat arguments `(q₁, len₁, q₂, len₂)` in a store of the acceptor (`AccStore`: the
  instance's functions, some LRAT state, the 1 MiB ABI memory `B₁`), the blocks in bounds and the
  arguments in `B₁`: the certificate is `words B₁ q₂ len₂`, the problem is held at `q₁` (`HoldsL`),
  read back as `words B₁ q₁ len₁` (`holdsL_words`) or `nestedAt B₁ q₁ len₁` with `NestedIn`
  (`holdsL_nested`). It is the generic `params_holds` (`…ListLift.Bump`) for the bump allocator
  `cabi_realloc` (`lratBump`: the kit's `BumpSpec.bumpAlloc`, from the kit's `realloc_sound`); the
  lowering writes only memory `1` and the allocator only the heap pointer, so the store stays a
  store of the acceptor;
* the core soundness theorems `Silmaril.Wasm.Examples.LratAccept.checkStream_sound` and
  `checkNested_sound`, which hold from any LRAT state.

**The bytes** (the kit's `decode_coreBytesOf`, `parse_compBytes` on kernel evaluations): `coreBytes`
decode to `prog` (`decode_coreBytes`) and `bytes` parse to `lratComp.toAst coreBytes`
(`bytes_parse`). That the reference reading of the parsed component
(`Silmaril.Project.WasmComponents.Ref.toRef?`) is `lratComp.toRef` is in
`Silmaril.Project.WasmComponents.LratAccept.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.LratAccept.Component

open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.Words (wd words)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (UnsatStream UnsatNested)

/-! ## The bytes -/

/-- **The core module bytes decode to `prog`.** -/
theorem decode_coreBytes : Silmaril.Wasm.Binary.Core.decode? coreBytes = some prog :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.decode_coreBytes

/-- **The component bytes parse to the emitted component.** -/
theorem bytes_parse :
    Silmaril.Wasm.Component.Binary.parse bytes = .ok (lratComp.toAst coreBytes) :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.bytes_parse

/-! ## The fragment and the allocator -/

/-- `lratComp` is well formed. -/
theorem lratComp_good : lratComp.Good :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.lratComp_good

/-- `accI` is the instance of `prog` that `acceptSound` assumes, with the ABI memory at
address `1`. -/
theorem lratComp_inst : lratComp.Inst accI :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.lratComp_inst

/-- **`cabi_realloc` is a bump allocator** (function address `10`, memory address `1`). -/
theorem lratBump (P : Profile) : BumpAlloc P 10 1 memBytes LInvL :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.lratBump P

/-- The instance store meets the invariant, with the heap pointer at `heapBase`. -/
theorem lInvL_init : LInvL accI.store heapBase :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.lInvL_init

/-! ## The memory lemma -/

/-- **The two lowered arguments in memory**: lowering a list of type `list<t>` and the
certificate words `cs` from the instance store, through the allocator (address `10`) into
memory address `1`, ends with the flat arguments `(q₁, len₁, q₂, len₂)` in a store of the
acceptor (`AccStore`, some LRAT state `G`, `B₀`, some heap pointer `top`, ABI memory `B₁`), the
blocks in bounds, the first list held at `q₁` and the certificate words at `q₂`. -/
theorem lowered {P : Profile} {t : LTy} {us : List LVal} {cs : List (BitVec 32)}
    {s : Store Nat} {fl : List Silmaril.Wasm.Execution.Core.Val}
    (hL : LParams P 10 1 [.list t, .list .s32] [.list us, LVal.ofWords cs] accI.store fl s) :
    ∃ q₁ q₂ G B₀ top B₁ lo hi, fl = [.i32 (BitVec.ofNat 32 q₁),
        .i32 (BitVec.ofNat 32 us.length), .i32 (BitVec.ofNat 32 q₂),
        .i32 (BitVec.ofNat 32 cs.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ cs.length < 2 ^ 32 ∧
      AccStore s G B₀ top B₁ ∧
      q₁ + us.length * t.size ≤ B₁.size ∧ HoldsL B₁ lo hi t us q₁ ∧
      q₂ + 4 * cs.length ≤ B₁.size ∧ words B₁ q₂ cs.length = cs :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.lower2 hL

/-- **The clauses of a lowered `list<list<s32>>` are the words of their blocks**, which lie in
memory. -/
theorem holdsL_nested {B : ByteArray} {lo hi : Nat} (p : List (List (BitVec 32))) (q : Nat)
    (h : HoldsL B lo hi (.list .s32) (p.map LVal.ofWords) q) :
    nestedAt B q p.length = p ∧
      ∀ i < p.length, (wd B (q + 8 * i)).toNat + 4 * (wd B (q + 8 * i + 4)).toNat ≤ B.size :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.holdsL_nested p q h

/-! ## Soundness of accepting calls -/

/-- **An accepting call of `check-stream` is on an unsatisfiable stream**, whatever the
certificate. -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef]) :
    xs ∈ UnsatStream :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.checkStream_sound P prof xs cs h

/-- **An accepting call of `check-nested` is on an unsatisfiable formula**, whatever the
certificate. -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef]) :
    p ∈ UnsatNested :=
  Silmaril.Proofs.Wasm.Examples.LratAccept.Component.checkNested_sound P prof p cs h

end Silmaril.Wasm.Examples.LratAccept.Component
