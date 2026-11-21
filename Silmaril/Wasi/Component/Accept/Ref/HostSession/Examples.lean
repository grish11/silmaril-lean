module

public import Silmaril.Wasi.Component.Accept.Ref.HostSession.Thms
public import Silmaril.Wasm.Component.Reference.HAcceptTuple.Thms
public import Silmaril.Wasi.Component.Accept.Ref.Typed.Examples
public import Silmaril.Wasi.Component.Accept.Consequence.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
import Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSessionTuple

/-! # Acceptance through a host import: the `tuple<u8, u8>` acceptor

`Reference.HAcceptTuple.tupleL` is the `HLinked2` mirror of `tupleHiBytes`'s core module and
import type. It is written by hand, not decoded from the bytes. At every profile `P` and
component choice profile `prof`, with the host `acceptG` (every call answered with no results):

* `tupleL_sessAcceptedIR`: the IR accepts `"hi"` (`[104, 105]`) on sessions at the host's
  answers. The witness is the execution-backed IR play `tupleL_ir_session`.
* `tupleL_sessAcceptedRef`: **the reference machine accepts `"hi"`**. Some session of
  `tupleL.toRef` on REF, under the logging host of `acceptG`, logs `accept` on arguments
  carrying `[104, 105]`. This follows from the IR side through `HLinked2.sessAccepted_iff`
  under `tupleL_adequate` and `tupleL_hostTyped`, not from a REF run.
* `tupleL_mem_posBytesLang`: `"hi"` is in the positional IR language.

**What links this to `tupleHiBytes`** (`decodeBinary_tupleHi`, kernel evaluation): the IR
lowering of `tupleHiBytes` (`ComponentAcceptor.decodeBinary`) is `tupleI.toComp`, except that the
core module is carried as a `Binary.CoreMod`. That `CoreMod` has `tupleI.mod`'s interface and
its bytes decode to `tupleCore`. So the bytes give exactly the IR component of the importer.

**What does not link yet** (the ledger):
* the core semantics: `Binary.coreModSem P` (`Param.engineSem` on `core3P P`) on that `CoreMod`
  against `impSem P` (`IsInstance`, `core3Sem P`) on `tupleI.mod`;
* the wrapper: `tupleI.toComp` against `tupleL.toComp`. `tupleL` is an `HLinked2`, whose
  adequacy theorem needs an exporter, here `setGetS`, which is never called;
* REF: `decodeValid tupleHiBytes` against `tupleL.toRef`;
* the typed environment of `AcceptedTypedBytes` against sessions.

Not shown: that no other string is accepted.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref.HostSessionExamples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HAcceptTuple
open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Numerics (Profile)

/-- The host import `accept`. -/
abbrev acceptIdx : Fin tupleL.host.length := ⟨0, by decide⟩

theorem tupleL_typed :
    SimpleI.TypedCalls tupleL.imp [(⟨0, by decide⟩, [])] := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  rfl

/-- **The IR accepts `"hi"` on sessions at the host's answers** (proved, every profile). -/
theorem tupleL_sessAcceptedIR (P : Profile) :
    HLinked2.SessAcceptedIR P tupleL acceptG () acceptIdx [104, 105] :=
  ⟨_, tupleL_typed, _, _, _, rfl, rfl, tupleL_ir_session P, tupleL_hostRun, _,
    List.mem_singleton_self _, _, _, rfl, rfl⟩

/-- **The reference machine accepts `"hi"`** (proved, every profile and component choice
profile, through `HLinked2.sessAccepted_iff`). -/
theorem tupleL_sessAcceptedRef (P : Profile) (prof : ProfileKind) :
    HLinked2.SessAcceptedRef P prof tupleL acceptG () acceptIdx [104, 105] :=
  (HLinked2.sessAccepted_iff tupleL_adequate tupleL_hostTyped).mpr (tupleL_sessAcceptedIR P)

/-- `"hi"` is in the positional IR language (proved, every profile). -/
theorem tupleL_mem_posBytesLang (P : Profile) :
    [104, 105] ∈ posBytesLang (tupleL.toComp.den (impSem P)) acceptIdx :=
  HLinked2.sessAcceptedIR_sub (tupleL_sessAcceptedIR P)

/-- **The IR lowering of `tupleHiBytes` is the importer `tupleI.toComp`** (proved, kernel
evaluation): its core module is a `CoreMod` with `tupleI.mod`'s interface whose bytes decode to
`tupleCore`. -/
theorem decodeBinary_tupleHi :
    ∃ cm : Silmaril.Wasm.Component.Binary.CoreMod,
      Silmaril.Wasi.Accept.ComponentAcceptor.decodeBinary
          Silmaril.Wasi.Accept.Ref.Examples.tupleHiBytes =
        some (.mk tupleI.imports [.core cm (SimpleI.lowerArgs tupleI.imports)]
          tupleI.toComp.exports) ∧
      CoreModule.imports cm = tupleI.mod.imports ∧ CoreModule.exports cm = tupleI.mod.exports ∧
      Silmaril.Wasm.Component.Binary.coreModule cm = tupleCore :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSessionTuple.decodeBinary_tupleHi

end Silmaril.Wasi.Accept.Ref.HostSessionExamples
