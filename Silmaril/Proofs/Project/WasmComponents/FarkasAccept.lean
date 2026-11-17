module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Examples.FarkasAccept.Component.Thms

/-!
# The Farkas acceptor component read from its bytes: proofs

`toRef_toAst`: the reference reading `toRef?` of the emitted component is `farkasComp.toRef`. The
core module section is read by `decode?`, which is `prog` on `coreBytes` (`decode_coreBytes`);
the other sections are closed terms, read by evaluation (`rfl`). `toRef_of_parse`: every
reference reading of what `bytes` parse to is `farkasComp.toRef` (`bytes_parse`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmComponents.FarkasAccept

open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Wasm.Examples.FarkasAccept.Component (decode_coreBytes bytes_parse)
open Silmaril.Project.WasmComponents.Ref (toRef? section_)
open Silmaril.Wasm.Component.Reference (Core3Component)

theorem section_coreBytes :
    section_ (.coreModule coreBytes) = some [.coreModule prog] := by
  simp [section_, decode_coreBytes]

theorem toRef_toAst : toRef? (farkasComp.toAst coreBytes) = some farkasComp.toRef := by
  unfold toRef?
  rw [show (farkasComp.toAst coreBytes).sections =
    .coreModule coreBytes :: (farkasComp.toAst coreBytes).sections.tail from rfl, List.mapM_cons,
    section_coreBytes]
  rfl

theorem toRef_of_parse {ast : Silmaril.Wasm.Component.Binary.Ast}
    (hp : Silmaril.Wasm.Component.Binary.parse bytes = .ok ast) {r : Core3Component}
    (hr : toRef? ast = some r) : r = farkasComp.toRef := by
  rw [bytes_parse] at hp
  cases hp
  rw [toRef_toAst] at hr
  cases hr
  rfl

end Silmaril.Proofs.Project.WasmComponents.FarkasAccept
