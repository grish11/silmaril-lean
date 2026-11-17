module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Examples.SatAccept.Component.Thms
import Silmaril.Proofs.Project.WasmComponents.SatAccept

/-!
# The SAT acceptor component read from its bytes

`Silmaril.Wasm.Examples.SatAccept.bytes` (the contents of
`examples/wasm-acceptors/sat_accept.wasm`, regenerated from it) parse to
`satComp.toAst coreBytes` (`bytes_parse`), whose reading by the reference semantics
(`Silmaril.Project.WasmComponents.Ref.toRef?`, core modules decoded by `Binary.Core.decode?`)
is `satComp.toRef` (`toRef_toAst`, by kernel evaluation). So the soundness of accepting calls
(`Silmaril.Wasm.Examples.SatAccept.checkStream_sound`, `checkNested_sound`) holds for **every**
reference component read from the bytes (`checkStream_sound_of_bytes`,
`checkNested_sound_of_bytes`): a call of `check-stream` returning `true` on `xs` and `ms` means
`satStream xs ms = true`, hence `xs ∈ SatStream`; a call of `check-nested` returning `true` on
`p` and `ms` means `satNested p ms = true`, hence `p ∈ SatNested`.

The file itself is tied to `bytes` by regeneration and the SHA-256 pinned in
`tools/wasm-acceptor-harness/suites/sat.json`, not by a theorem here.

Proofs in `Silmaril.Proofs.Project.WasmComponents.SatAccept`.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.SatAccept

open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift (LVal)
open Silmaril.Project.WasmComponents.Ref (toRef?)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (satStream satNested SatStream SatNested)

/-- **The reference reading of the emitted component is `satComp.toRef`.** -/
theorem toRef_toAst : toRef? (satComp.toAst coreBytes) = some satComp.toRef :=
  Silmaril.Proofs.Project.WasmComponents.SatAccept.toRef_toAst

/-- Every reference reading of what the bytes parse to is `satComp.toRef`. -/
theorem toRef_of_parse {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) : r = satComp.toRef :=
  Silmaril.Proofs.Project.WasmComponents.SatAccept.toRef_of_parse hp hr

/-- **Accepting `check-stream` calls of the component read from the bytes are sound.** -/
theorem checkStream_sound_of_bytes {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) (P : Profile) (prof : ProfileKind) (xs ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords ms).toRef]) :
    satStream xs ms = true ∧ xs ∈ SatStream := by
  obtain rfl := toRef_of_parse hp hr
  exact ⟨checkStream_sound P prof xs ms h, checkStream_satStream P prof xs ms h⟩

/-- **Accepting `check-nested` calls of the component read from the bytes are sound.** -/
theorem checkNested_sound_of_bytes {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) (P : Profile) (prof : ProfileKind)
    (p : List (List (BitVec 32))) (ms : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords ms).toRef]) :
    satNested p ms = true ∧ p ∈ SatNested := by
  obtain rfl := toRef_of_parse hp hr
  exact ⟨checkNested_sound P prof p ms h, checkNested_satNested P prof p ms h⟩

end Silmaril.Project.WasmComponents.SatAccept
