module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Acceptor.Bridge.Thms
import Silmaril.Proofs.Project.WasmComponents.Acceptor

/-!
# List components read from their bytes

For **every** list-taking component `c` (`Silmaril.Wasm.Component.Reference.ListLift.ListComp`):
the reference reading `toRef?` (`Silmaril.Project.WasmComponents.Ref`, core modules decoded by
`Binary.Core.decode?`) of the emitted binary component `c.toAst core` is `c.toRef` whenever
`core` decodes to `c.mod` (`toRef_toAst`). Proved once, by reading the sections in order (the
type sections item by item, the binary items of every `LTy` as the reference definitions); no
per-component evaluation is needed. So for bytes parsing to `c.toAst core`, every reference
reading of what they parse to is `c.toRef` (`toRef_of_parse`), and the soundness of a checker
export holds for it (`CheckerExport.sound_of_bytes`: the acceptor kit's
`Silmaril.Wasm.Acceptor.CheckerExport.sound` on the component read from the bytes).

The per-acceptor facts are `decode? coreBytes = some prog` and `parse bytes = .ok (c.toAst
coreBytes)` (`Silmaril.Wasm.Acceptor.decode_coreBytesOf`, `parse_compBytes` on kernel
evaluations). A registered file is tied to its `bytes` by a component-value certificate
(`Silmaril.Project.WasmComponents.is_of_encode`; for the acceptors, in
`ProjectSelfTest.WasmAcceptors`).

Proofs in `Silmaril.Proofs.Project.WasmComponents.Acceptor`.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Acceptor

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift (ListComp LVal)
open Silmaril.Wasm.Acceptor (Kit CheckerExport)
open Silmaril.Project.WasmComponents.Ref (toRef?)
open Silmaril.Wasm.Numerics (Profile)

/-- **The reference reading of an emitted list component is its reference component.** -/
theorem toRef_toAst (c : ListComp) {core : ByteArray}
    (h : Silmaril.Wasm.Binary.Core.decode? core = some c.mod) :
    toRef? (c.toAst core) = some c.toRef :=
  Silmaril.Proofs.Project.WasmComponents.Acceptor.toRef_toAst c h

/-- **Every reference reading of what the bytes parse to is the reference component.** -/
theorem toRef_of_parse (c : ListComp) {core bytes : ByteArray}
    (hdec : Silmaril.Wasm.Binary.Core.decode? core = some c.mod)
    (hparse : Binary.parse bytes = .ok (c.toAst core)) {ast : Binary.Ast}
    (hp : Binary.parse bytes = .ok ast) {r : Core3Component} (hr : toRef? ast = some r) :
    r = c.toRef :=
  Silmaril.Proofs.Project.WasmComponents.Acceptor.toRef_of_parse c hdec hparse hp hr

/-- **Accepting calls of a checker export of the component read from the bytes.** -/
theorem CheckerExport.sound_of_bytes {c : ListComp} {α β : Type} (K : Kit c)
    (e : CheckerExport c α β) (hc : e.CoreSound K) {core bytes : ByteArray}
    (hdec : Silmaril.Wasm.Binary.Core.decode? core = some c.mod)
    (hparse : Binary.parse bytes = .ok (c.toAst core)) {ast : Binary.Ast}
    (hp : Binary.parse bytes = .ok ast) {r : Core3Component} (hr : toRef? ast = some r)
    (P : Profile) (prof : ProfileKind) (p : α) (q : β)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () r []
      e.x.name ((e.enc p q).map LVal.toRef)) :
    e.Goal p q := by
  obtain rfl := toRef_of_parse c hdec hparse hp hr
  exact e.sound K hc P prof p q h

end Silmaril.Project.WasmComponents.Acceptor
