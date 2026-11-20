module

public import Silmaril.Wasi.Component.Accept.Ref.HostSession.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession

/-! # Acceptance through a host import, REF sessions against IR plays: theorems

**Scope** (`Defs`): `HLinked2` components (a core module with host imports, optionally linked to
an import-free exporter; scalar/record/variant types, no linear memory, no start function), an
`accept` host import `a`, and the logging host of `g`. Built on the finite session adequacy of
#782 (`HLinked2.sessAdequacy_full`) and on (P2) (`bytesOf?_toRefVal`).

## Proved

* `bytesOf?_map_toRefVal`: on argument lists, `bytesOf? (ws.map toRefVal) = args1 bytes? ws`.
* `HLinked2.sessAccepted_iff` (every profile `P` and component choice profile, under
  `HLinked2.Adequate` and `HLinked2.HostTyped g`): **REF session acceptance equals IR session
  acceptance at the host's answers**. Some session of typed calls of `l.toRef` on the reference
  machine logs an `accept` call carrying `w` iff some session play of
  `l.toComp.den (impSem P)`, its host calls answered as `g` answers them, has an answered
  `accept` call carrying `w`.
* `HLinked2.sessAcceptedIR_sub` and `HLinked2.sessAcceptedRef_sub`: such a `w` is in the
  positional IR language `posBytesLang (l.toComp.den (impSem P)) a` (plays with any environment
  answers). Only this inclusion holds in general (`Defs`, "Why the host's answers are part of
  the IR side").

## Hypotheses, all explicit

* `HLinked2.Adequate`: the fragment conditions of #782 (`Good`, `Inst` with no start function,
  flat arities, float-free types, well-typed wiring, generated names avoided, injective wiring,
  core modules without memories, tables or data).
* `HLinked2.HostTyped g`: the host answers in the IR's result types. An ill-typed answer is an
  `internal` fault of REF, not a trap (`HLinkedSession.Thms`).
* Typed calls (`SimpleI.TypedCalls`) inside both definitions. NaNs are excluded by the
  float-free condition. The theorems hold at every component choice profile `prof`.

## Not proved (the ledger, `docs/projects/component-caveats.md`)

* Plays that stop inside a call (an `accept` call followed by divergence) and calls that are
  never completed: sessions observe completed calls only.
* The typed environment of `AcceptedTypedBytes` (`Steps` with `TypedEnvLabel`, any
  interleaving of invocations, ticks and cancellations, the host `acceptLinkedProgAt`) against
  `HLinked2.sessObs` (sequential sessions under `answerHostS`).
* The named view: `posBytesLang` of `den` against `bytesLang` of `Layout.compModel`
  (`denU` through `atSizes`, `lowerH`, `upH`).
* Binaries: `decodeValid b` and `ComponentAcceptor.decodeBinary b` (a `Comp CoreMod` under
  `Binary.coreModSem P`, `Param.engineSem` over `core3P P`) against `l.toRef` and `l.toComp`
  (a `Comp ImpModule` under `impSem P`). No translation from bytes to `HLinked2` exists.
  `Examples` narrows this gap for `tupleHiBytes` (`decodeBinary_tupleHi`) and gives a concrete
  instance of the hypotheses with an execution-backed acceptance of `"hi"`.
-/

public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-- **REF and the IR read the bytes of an argument list the same way** (proved). -/
theorem bytesOf?_map_toRefVal (ws : List IVal) : bytesOf? (ws.map toRefVal) = args1 bytes? ws :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession.bytesOf?_map_toRefVal ws

namespace HLinked2

variable {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind} {l : HLinked2} {σ : Type}
  {g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId → List RVal → Option (List RVal × σ)}
  {s₀ : σ} {a : Fin l.host.length} {w : List UInt8}

/-- **Session acceptance through a host import: REF = IR at the host's answers** (proved, every
profile and component choice profile, `HLinked2.Adequate`, typed host). -/
theorem sessAccepted_iff (hl : l.Adequate) (hT : l.HostTyped g) :
    SessAcceptedRef P prof l g s₀ a w ↔ SessAcceptedIR P l g s₀ a w :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession.sessAccepted_iff hl hT

/-- **IR session acceptance is in the positional IR language** (proved, every profile). -/
theorem sessAcceptedIR_sub (h : SessAcceptedIR P l g s₀ a w) :
    w ∈ posBytesLang (l.toComp.den (impSem P)) a :=
  Silmaril.Proofs.Wasi.Component.Accept.Ref.HostSession.sessAcceptedIR_sub h

/-- **REF session acceptance is in the positional IR language** (proved, every profile and
component choice profile, `HLinked2.Adequate`, typed host): every byte string a session of the
reference machine logs at `accept` is carried by an `accept` question of a play of the IR. -/
theorem sessAcceptedRef_sub (hl : l.Adequate) (hT : l.HostTyped g)
    (h : SessAcceptedRef P prof l g s₀ a w) : w ∈ posBytesLang (l.toComp.den (impSem P)) a :=
  sessAcceptedIR_sub ((sessAccepted_iff hl hT).mp h)

end HLinked2

end Silmaril.Wasi.Accept.Ref
