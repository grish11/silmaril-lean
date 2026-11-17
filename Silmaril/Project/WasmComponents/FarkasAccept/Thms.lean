module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Examples.FarkasAccept.Component.Thms
import Silmaril.Proofs.Project.WasmComponents.FarkasAccept

/-!
# The Farkas acceptor component read from its bytes

`Silmaril.Wasm.Examples.FarkasAccept.bytes` (the contents of
`examples/wasm-acceptors/farkas_accept.wasm`, regenerated from it) parse to
`farkasComp.toAst coreBytes` (`bytes_parse`), whose reading by the reference semantics
(`Silmaril.Project.WasmComponents.Ref.toRef?`, core modules decoded by `Binary.Core.decode?`)
is `farkasComp.toRef` (`toRef_toAst`, by kernel evaluation). So the soundness of accepting calls
(`Silmaril.Wasm.Examples.FarkasAccept.Component.check_sound`) holds for **every** reference
component read from the bytes (`check_sound_of_bytes`): a call of `check` returning `true` on
the `list<ineq>` value of a system `S` and any multipliers `y` means `S ∈ Infeasible`.

The file itself is tied to `bytes` by regeneration and the SHA-256 pinned in
`tools/wasm-acceptor-harness/suites/farkas.json`, not by a theorem here.

Proofs in `Silmaril.Proofs.Project.WasmComponents.FarkasAccept`.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.FarkasAccept

open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Project.WasmComponents.Ref (toRef?)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.LinArith.Carrier (SystemW S64 Infeasible)

/-- **The reference reading of the emitted component is `farkasComp.toRef`.** -/
theorem toRef_toAst : toRef? (farkasComp.toAst coreBytes) = some farkasComp.toRef :=
  Silmaril.Proofs.Project.WasmComponents.FarkasAccept.toRef_toAst

/-- Every reference reading of what the bytes parse to is `farkasComp.toRef`. -/
theorem toRef_of_parse {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) : r = farkasComp.toRef :=
  Silmaril.Proofs.Project.WasmComponents.FarkasAccept.toRef_of_parse hp hr

/-- **Accepting `check` calls of the component read from the bytes are sound.** -/
theorem check_sound_of_bytes {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) (P : Profile) (prof : ProfileKind) (S : SystemW) (y : List S64)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      "check" [(ofSystem S).toRef, (ofS64s y).toRef]) :
    S ∈ Infeasible := by
  obtain rfl := toRef_of_parse hp hr
  exact Silmaril.Wasm.Examples.FarkasAccept.Component.check_sound P prof S y h

end Silmaril.Project.WasmComponents.FarkasAccept
