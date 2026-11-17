module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Examples.LratAccept.Component.Thms
public import Silmaril.Project.WasmComponents.Acceptor.Thms

/-!
# The LRAT acceptor component read from its bytes

`Silmaril.Wasm.Examples.LratAccept.bytes` (the contents of
`examples/wasm-acceptors/lrat_accept.wasm`, regenerated from it) parse to
`lratComp.toAst coreBytes` (`bytes_parse`), whose reading by the reference semantics
(`Silmaril.Project.WasmComponents.Ref.toRef?`, core modules decoded by `Binary.Core.decode?`)
is `lratComp.toRef` (`toRef_toAst`: the acceptor kit's generic
`Silmaril.Project.WasmComponents.Acceptor.toRef_toAst`, for every list component, with
`decode_coreBytes`). So the soundness of accepting calls
(`Silmaril.Wasm.Examples.LratAccept.Component.checkStream_sound`, `checkNested_sound`) holds
for **every** reference component read from the bytes (`checkStream_sound_of_bytes`,
`checkNested_sound_of_bytes`): a call of `check-stream` returning `true` on `xs` and any
certificate `cs` means `xs ∈ UnsatStream`; a call of `check-nested` returning `true` on `p` and
any certificate `cs` means `p ∈ UnsatNested`.

The file itself is tied to `bytes` by regeneration and the SHA-256 pinned in
`tools/wasm-acceptor-harness/suites/lrat.json`, not by a theorem here.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.LratAccept

open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift (LVal)
open Silmaril.Project.WasmComponents.Ref (toRef?)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (UnsatStream UnsatNested)

/-- **The reference reading of the emitted component is `lratComp.toRef`.** -/
theorem toRef_toAst : toRef? (lratComp.toAst coreBytes) = some lratComp.toRef :=
  Silmaril.Project.WasmComponents.Acceptor.toRef_toAst lratComp
    Silmaril.Wasm.Examples.LratAccept.Component.decode_coreBytes

/-- Every reference reading of what the bytes parse to is `lratComp.toRef`. -/
theorem toRef_of_parse {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) : r = lratComp.toRef :=
  Silmaril.Project.WasmComponents.Acceptor.toRef_of_parse lratComp
    Silmaril.Wasm.Examples.LratAccept.Component.decode_coreBytes
    Silmaril.Wasm.Examples.LratAccept.Component.bytes_parse hp hr

/-- **Accepting `check-stream` calls of the component read from the bytes are sound.** -/
theorem checkStream_sound_of_bytes {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) (P : Profile) (prof : ProfileKind) (xs cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef]) :
    xs ∈ UnsatStream := by
  obtain rfl := toRef_of_parse hp hr
  exact Silmaril.Wasm.Examples.LratAccept.Component.checkStream_sound P prof xs cs h

/-- **Accepting `check-nested` calls of the component read from the bytes are sound.** -/
theorem checkNested_sound_of_bytes {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) (P : Profile) (prof : ProfileKind)
    (p : List (List (BitVec 32))) (cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef]) :
    p ∈ UnsatNested := by
  obtain rfl := toRef_of_parse hp hr
  exact Silmaril.Wasm.Examples.LratAccept.Component.checkNested_sound P prof p cs h

end Silmaril.Project.WasmComponents.LratAccept
