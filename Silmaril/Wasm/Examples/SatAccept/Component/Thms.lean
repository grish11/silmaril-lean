module

public import Silmaril.Wasm.Examples.SatAccept.Component.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Proofs.Wasm.Examples.SatAccept.Component.Sound
import Silmaril.Proofs.Wasm.Examples.SatAccept.Component.Bytes

/-!
# The SAT model-witness acceptor as a component: theorems

**Accepting calls are sound**, for the reference machine at every numerics profile `P` and
every component choice profile `prof`:

* `checkStream_sound`: if calling `check-stream` of `satComp.toRef` on the `list<s32>` values
  of the words `xs` and `ms` can return `true`, then `satStream xs ms = true`; so `xs` is in
  `SatStream` (`checkStream_satStream`), with the model witness `ms` (`checkStream_accepts`);
* `checkNested_sound`, `checkNested_satNested`, `checkNested_accepts`: the same for
  `check-nested` on a `list<list<s32>>` value `p`, with `satNested` and `SatNested`.

Only accepting behaviours are constrained: traps, divergence and `false` answers are not (no
completeness is claimed).

The proof (`Silmaril.Proofs.Wasm.Examples.SatAccept.Component`) combines

* `acceptSound satComp` (`Silmaril.Wasm.Component.Reference.ListLift`), whose hypotheses are
  `satComp_good` and `satComp_inst` (the instance `satI` of `prog`, by kernel evaluation);
* the **memory lemma** `lowered`: the lowering of the two arguments ends with the flat
  arguments `(q₁, len₁, q₂, len₂)`, memory `0` of `memBytes` bytes `B`, the heap pointer
  present, the blocks in bounds, and the arguments in memory: the model is `words B q₂ len₂`,
  and the problem is held at `q₁` (`HoldsL`), read back as `words B q₁ len₁` (`holdsL_words`)
  or `nestedAt B q₁ len₁` with `NestedIn` (`holdsL_nested`). It is the generic
  `params_holds` (`…ListLift.Bump`) for the bump allocator `cabi_realloc` (`satBump`, from
  `realloc_returns`);
* the core specifications `stream_returns`, `nested_returns` and the carrier soundness
  `satStream_sound`, `satNested_sound`.

**The bytes** (by kernel evaluation): `coreBytes` decode to `prog` (`decode_coreBytes`) and
`bytes` parse to `satComp.toAst coreBytes` (`bytes_parse`). That the reference reading of the
parsed component (`Silmaril.Project.WasmComponents.Ref.toRef?`) is `satComp.toRef` is in
`Silmaril.Project.WasmComponents.SatAccept.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Logic.Words (wd words)
open Silmaril.Wasm.Logic.VC (globalVal)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (satStream satNested SatStream SatNested Accepts)

/-! ## The bytes -/

/-- **The core module bytes decode to `prog`.** -/
theorem decode_coreBytes : Silmaril.Wasm.Binary.Core.decode? coreBytes = some prog :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.decode_coreBytes

/-- **The component bytes parse to the emitted component.** -/
theorem bytes_parse :
    Silmaril.Wasm.Component.Binary.parse bytes = .ok (satComp.toAst coreBytes) :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.bytes_parse

/-! ## The fragment and the allocator -/

/-- `satComp` is well formed. -/
theorem satComp_good : satComp.Good :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.satComp_good

/-- `satI` is the instance of `prog` that `acceptSound` assumes. -/
theorem satComp_inst : satComp.Inst satI :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.satComp_inst

/-- **`cabi_realloc` is a bump allocator** (function address `0`, memory `0`). -/
theorem satBump (P : Profile) : BumpAlloc P 0 0 memBytes SInv :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.satBump P

/-- The instance store meets the invariant, with the heap pointer at `heapBase`. -/
theorem sInv_init : SInv satI.store heapBase :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.sInv_init

/-! ## The memory lemma -/

/-- **The two lowered arguments in memory**: lowering a list of type `list<t>` and the model
words `ms` from the instance store ends with the flat arguments `(q₁, len₁, q₂, len₂)`, the
functions of the instance, memory `0` of `memBytes` bytes `B`, the heap pointer present, the
blocks in bounds, the first list held at `q₁` and the model words at `q₂`. -/
theorem lowered {P : Profile} {t : LTy} {us : List LVal} {ms : List (BitVec 32)}
    {s : Store Nat} {fl : List Silmaril.Wasm.Execution.Core.Val}
    (hL : LParams P 0 0 [.list t, .list .s32] [.list us, LVal.ofWords ms] satI.store fl s) :
    ∃ q₁ q₂ mt B lo hi, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 us.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 ms.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ ms.length < 2 ^ 32 ∧
      s.funcs = satI.store.funcs ∧ s.mems[0]? = some ⟨mt, B⟩ ∧ B.size = memBytes ∧
      (globalVal s satM 0).isSome ∧
      q₁ + us.length * t.size ≤ B.size ∧ HoldsL B lo hi t us q₁ ∧
      q₂ + 4 * ms.length ≤ B.size ∧ words B q₂ ms.length = ms :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.lower2 hL

/-- **The clauses of a lowered `list<list<s32>>` are the words of their blocks**, which lie in
memory. -/
theorem holdsL_nested {B : ByteArray} {lo hi : Nat} (p : List (List (BitVec 32))) (q : Nat)
    (h : HoldsL B lo hi (.list .s32) (p.map LVal.ofWords) q) :
    nestedAt B q p.length = p ∧
      ∀ i < p.length, (wd B (q + 8 * i)).toNat + 4 * (wd B (q + 8 * i + 4)).toNat ≤ B.size :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.holdsL_nested p q h

/-! ## Soundness of accepting calls -/

/-- **An accepting call of `check-stream` answers `satStream`.** -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    satStream xs ms = true :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.checkStream_sound P prof xs ms h

/-- **An accepting call of `check-stream` has a model witness**: `ms`. -/
theorem checkStream_accepts (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    xs ∈ Accepts satStream :=
  ⟨ms, checkStream_sound P prof xs ms h⟩

/-- **An accepting call of `check-stream` is on a satisfiable stream.** -/
theorem checkStream_satStream (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    xs ∈ SatStream :=
  Silmaril.Logic.SAT.Carrier.satStream_sound (checkStream_accepts P prof xs ms h)

/-- **An accepting call of `check-nested` answers `satNested`.** -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    satNested p ms = true :=
  Silmaril.Proofs.Wasm.Examples.SatAccept.Component.checkNested_sound P prof p ms h

/-- **An accepting call of `check-nested` has a model witness**: `ms`. -/
theorem checkNested_accepts (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    p ∈ Accepts satNested :=
  ⟨ms, checkNested_sound P prof p ms h⟩

/-- **An accepting call of `check-nested` is on a satisfiable formula.** -/
theorem checkNested_satNested (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () satComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    p ∈ SatNested :=
  Silmaril.Logic.SAT.Carrier.satNested_sound (checkNested_accepts P prof p ms h)

end Silmaril.Wasm.Examples.SatAccept
