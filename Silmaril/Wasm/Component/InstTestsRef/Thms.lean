module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Wasm.Component.InstTests.Thms
import Silmaril.Proofs.Wasm.Component.InstTestsRef.Ref

/-!
# Component test binaries on the reference machine: agreement on these two examples

All proved; proofs in `Silmaril.Proofs.Wasm.Component.InstTestsRef`.

**From the bytes to the reference syntax.** `decodeRef_starts`, `decodeRef_trap`: the existing
decoder `Conformance.decodeRef` (`Binary.parse`, then `Conformance.toRef`, core modules by the core
decoder) reads `startsBytes` and `trapBytes` as `startsRef` and `trapRef` (one definitional check
by the kernel). `starts_valid`, `trap_valid`: the reference validator `check? Features.p2`
accepts them, so `Wasi.Accept.Ref.decodeValid` accepts the bytes.

**Agreement.** Each theorem pairs the binary's play under the instantiating IR (`InstTests.Thms`,
on `Binary.parseComponent` of the bytes) with an **executed** run of the reference machine on the
component `decodeRef` returns for the same bytes (`decide +kernel` on its executable drivers,
then their soundness theorems):

* `starts_agree` (every profile `P` on the IR side): the IR instantiation of the lowered
  `starts.wasm` calls `f(1)`, `f(2)`, is ready, and `get()` answers `42`; `decodeRef` reads the
  bytes as a valid component which the reference machine, under the logging host `embL` with
  `f: func(x: u32)` (`hostConfigX`), instantiates with the host log `logOfCalls startsTrace`
  (the same two calls, in the same order), after which `get()` returns `u32 42`;
* `trap_agree` (every profile `P` on the IR side): the IR instantiation of the lowered
  `trap.wasm` fails; `decodeRef` reads the bytes as a valid component whose instantiation on the
  reference machine traps.

**Scope.** These are agreements on two examples, one IR play against one reference run each
(the reference runs use the Core 3.0 stepper of `core3 neverFail` with the first scheduling
oracle). Both sides start from the same bytes, through two decoders: `Binary.parseComponent`
(the IR's lowering) and `Conformance.decodeRef` (the reference syntax). For every binary they
share the parser and agree on core instantiations (`DecoderBridge.rel_of_decode`, structural
only). Nothing is proved about how `toRef` relates to the reference's own reading of `Binary.md`,
and no general theorem relating `Comp.denI` to the reference machine's instantiation is claimed
(the open goals are `DecoderBridge.Task.failAdequacy` and `Task.startAdequacy`).
-/

public section

namespace Silmaril.Wasm.Component.InstTestsRef

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.Numerics (Profile)

/-- **`decodeRef` reads `starts.wasm` as `startsRef`.** -/
theorem decodeRef_starts : decodeRef startsBytes = .ok startsRef :=
  Silmaril.Proofs.Wasm.Component.InstTestsRef.decodeRef_starts

/-- **`decodeRef` reads `trap.wasm` as `trapRef`.** -/
theorem decodeRef_trap : decodeRef trapBytes = .ok trapRef :=
  Silmaril.Proofs.Wasm.Component.InstTestsRef.decodeRef_trap

/-- `startsRef` is valid. -/
theorem starts_valid : ∃ ct, Valid Features.p2 startsRef ct :=
  Silmaril.Proofs.Wasm.Component.InstTestsRef.starts_valid

/-- `trapRef` is valid. -/
theorem trap_valid : ∃ ct, Valid Features.p2 trapRef ct :=
  Silmaril.Proofs.Wasm.Component.InstTestsRef.trap_valid

/-- **`starts`: the IR on the lowered bytes and the reference machine on the decoded bytes make
the same host calls in the same order, and answer `get()` with `42`.** -/
theorem starts_agree (P : Profile) :
    instPlay (F := sigU) startsTrace .ready ++ [askEx getV, ansEx getV v42] ∈
        startsComp.denI (Binary.coreModSemI P) ∧
      ∃ c, decodeRef startsBytes = .ok c ∧ (∃ ct, Valid Features.p2 c ct) ∧
        (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
            ((), logOfCalls startsTrace)) ∈
          sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX c (importArgs hostI)
            [("get", [])] :=
  ⟨starts_inst P, startsRef, decodeRef_starts, starts_valid,
    Silmaril.Proofs.Wasm.Component.InstTestsRef.starts_ref⟩

/-- **`trap`: the IR instantiation of the lowered bytes fails and the reference machine's
instantiation of the decoded bytes traps.** -/
theorem trap_agree (P : Profile) :
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
        trapComp.denI (Binary.coreModSemI P) ∧
      ∃ c, decodeRef trapBytes = .ok c ∧ (∃ ct, Valid Features.p2 c ct) ∧
        InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX c
          (importArgs hostI) :=
  ⟨trap_inst P, trapRef, decodeRef_trap, trap_valid,
    Silmaril.Proofs.Wasm.Component.InstTestsRef.trap_ref⟩

end Silmaril.Wasm.Component.InstTestsRef
