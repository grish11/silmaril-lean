module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs

/-!
# The two readings of a component binary: the behavioural statements

`DecoderBridge.Thms` relates the two readings of a binary syntactically (`Rel`: the same core
modules are instantiated in the same order). What is not proved is that the IR's instantiation
semantics `Comp.denI (Binary.coreModSemI P)` of the IR reading and the reference machine's
behaviours on the REF reading agree on every binary. The two goals below state it for the
class of binaries the test binaries belong to, as `Prop`s:

* `Task.failAdequacy`: a binary importing exactly `f: func(u32)` (`InstLitmus.hostI`) whose
  REF reading is valid, and whose IR instantiation fails before any host call, traps on the
  reference machine under the logging host (`InstRef.embL`, `InstTestsRef.hostConfigX`);
* `Task.startAdequacy`: for such a binary **whose REF reading is in the fragment**
  `DecoderBridge.InFrag` (`Wire.Defs`), if the IR instantiation makes the host calls `t`, each
  answered `()`, becomes ready, and the IR's first export answers a call with no arguments with
  the values `ws`, then the reference machine instantiates the REF reading with the host log
  `InstRef.logOfCalls t` (the same calls in the same order), after which the export of that
  name returns `ws`. **This statement is false** (`DecoderBridge.ParamName.not_startAdequacy`):
  see below;
* `Task.startAdequacyChecked`: the corrected statement, `Task.startAdequacy` for binaries whose
  REF reading passes the reference machine's root checks (`RootChecked`).

The fragment hypothesis of `Task.startAdequacy` was added after the first statement, which had
none: there, the IR's first export may be a function of an **exported instance**, which the IR
reading names `instance#function` and the reference machine does not report as a function
export at all (`DecoderBridge.InstExport`, on a real binary: a demonstrated mismatch of the two
readings, not a disproof). Comparing such exports needs an export-path lookup on the reference
side, which `InstTestsRef.sessRunFrom` does not have; that comparison is not stated here. Within
the fragment, both readings name the same imports, exports, modules and wiring
(`DecoderBridge.relW_of_decode`), up to the parameter names of function types, which the IR
reading drops (below).

## Parameter names: the corrected domain

The IR reading drops the parameter names of component function types (`Binary.Lower`), so
`c.imports = hostI` holds for an import `f: func(y: u32)` too. The reference machine links the
root import against the host function `f: func(x: u32)` (`InstTestsRef.hostConfigX`) and its
import pre-check (`Instantiate.precheckImports`) compares parameter names: it traps before any
side effect. `paramname.wasm` (`DecoderBridge.ParamName`, `starts.wasm` with the parameter named
`y`) has the IR reading of `starts.wasm`, a valid REF reading in `InFrag`, and no finishing
reference instantiation, so `Task.startAdequacy` is false.

`RootChecked r` (decidable, `rootChecked r = true`) is the compatibility certificate of the
supported domain: the reference machine's own root checks of `r` against the host's arguments
`importArgs hostI`, run on the store at which the root instantiation runs them, pass (every
import supplied, `Instantiate.argsComplete`; the pre-check succeeds). It is exactly what the
root instantiation checks first, so outside it the reference instantiation traps
(`DecoderBridge.ParamName.traps_of_not_rootChecked`); the failure goal needs no such hypothesis.

Both use the deterministic IR profile `profile neverFail` (memory growth never fails), the
growth oracle of the reference stepper `core3 neverFail`; at other profiles the IR may fail a
`memory.grow` the reference performs. The reference side is existential (some run, first
scheduling oracle), as in `InstTestsRef`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **Open goal**: on binaries importing `f: func(u32)` with a valid REF reading, an IR
instantiation that fails before any host call traps on the reference machine. -/
def Task.failAdequacy : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    c.imports = hostI →
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI)

/-- **False** (`DecoderBridge.ParamName.not_startAdequacy`; kept as the record of the statement): on
binaries importing `f: func(u32)` with a valid REF reading in the fragment `InFrag`, the host
calls of a successful IR instantiation, and the answer of its first export to a call with no
arguments, are those of a reference run. The corrected statement is `Task.startAdequacyChecked`. -/
def Task.startAdequacy : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (n : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    InFrag r → c.imports = hostI → (c.exports.map (·.name)).head? = some n → (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(n, [])]

/-! ## The corrected domain -/

/-- **The root compatibility certificate**, as a Boolean (kernel-checkable): the reference
machine's root checks of `r` against the arguments `importArgs hostI` pass, on the store at which
`Instantiate.instantiateRoot` runs them (`hostConfigX`'s, the nesting depth incremented). -/
def rootChecked (r : RefComponent) : Bool :=
  Instantiate.argsComplete r (importArgs (E := Engine.core3 neverFail) hostI) &&
    (Instantiate.precheckImports (Canon.DispatchSt.incNestingSt hostConfigX.store)
      (importArgs hostI) Instantiate.Frame.empty r).toBool

/-- **The root compatibility certificate**: the reference machine's root checks of `r` (every
import supplied, import types matching, parameter names included) pass. -/
def RootChecked (r : RefComponent) : Prop := rootChecked r = true

instance (r : RefComponent) : Decidable (RootChecked r) :=
  inferInstanceAs (Decidable (rootChecked r = true))

/-- **Open goal, the corrected start goal**: `Task.startAdequacy` on binaries whose REF reading
passes the root checks (`RootChecked`). -/
def Task.startAdequacyChecked : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (n : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    InFrag r → RootChecked r → c.imports = hostI → (c.exports.map (·.name)).head? = some n →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(n, [])]

end Silmaril.Wasm.Component.DecoderBridge
