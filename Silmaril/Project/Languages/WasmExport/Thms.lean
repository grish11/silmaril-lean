module

public import Silmaril.Project.Languages.WasmExport.Defs
public import Silmaril.Wasm.Examples.JsonAccept.Exact.Thms
public import Silmaril.Wasm.Examples.EmptyCheck.Thms
public import Silmaril.Wasm.Examples.MemberCheck.Thms

/-!
# Languages of Wasm modules: laws of the export interpretations, and the JSON-subset acceptor

* The combined export interpretation is the accepted inputs without the rejected ones
  (`exportAcceptSafely_eq_diff`), and is Silmaril's generic combined verdict of one runner
  (`exportAcceptSafely_eq_acceptsSafely`).
* For the verified module `Silmaril.Wasm.Examples.JsonAccept.prog`, the three export
  interpretations are exact (`jsonAccept_exportAccept`, `jsonAccept_exportReject`,
  `jsonAccept_exportAcceptSafely`): the integer texts `intText` shorter than `2 ^ 32`, the other
  strings shorter than `2 ^ 32`, and the integer texts again. These restate
  `Silmaril.Wasm.Examples.JsonAccept.exportAccepted_eq` and its companions at the admitted hosts
  `allHosts`.

* For the checkers, through the export `check`: `EmptyCheck.prog` accepts nothing, at every
  host set (`emptyCheck_checkAccept`, no host assumption), and rejects every string shorter than
  `2 ^ 32` (`emptyCheck_checkReject`, which uses that the host set is nonempty).
  `MemberCheck.prog` accepts a subset of `memberLang` (`memberCheck_checkAccept_subset`, every
  host set), and exactly `memberLang` below `2 ^ 32`, rejecting exactly the rest below `2 ^ 32`
  (`memberCheck_checkAccept`, `memberCheck_checkReject`; nonempty host set). Inputs are byte
  strings (`UInt8`).

These are facts about the module AST. A registered artifact inherits them only through a
checked claim that its bytes decode to that AST (a value's `.is` problem).
-/

@[expose] public section

namespace Silmaril.Project.Languages.WasmExport

open Silmaril.Wasm.Game.Accept Silmaril.Wasm.Examples.JsonAccept

theorem exportAcceptSafely_eq_diff (m : Silmaril.Wasm.Module) :
    exportAcceptSafely m = exportAccept m \ exportReject m := rfl

theorem exportAcceptSafely_eq_acceptsSafely (m : Silmaril.Wasm.Module) :
    exportAcceptSafely m = Silmaril.Accept.acceptsSafely
      (exportRun (Silmaril.Wasm.Numerics.Profile.spec) allHosts m acceptExport) {1} {0} :=
  exportAcceptedNotRejected_eq_acceptsSafely

/-- Some Core host relation: the one with no outcome (`allHosts` is not empty). -/
theorem nohost_mem_allHosts : (fun _ _ _ _ => False) ∈ allHosts := Set.mem_univ _

theorem jsonAccept_exportAccept :
    exportAccept prog = {w | w ∈ intText ∧ w.length < 2 ^ 32} :=
  exportAccepted_eq nohost_mem_allHosts

theorem jsonAccept_exportReject :
    exportReject prog = {w | w ∉ intText ∧ w.length < 2 ^ 32} :=
  exportRejected_eq nohost_mem_allHosts

theorem jsonAccept_exportAcceptSafely :
    exportAcceptSafely prog = {w | w ∈ intText ∧ w.length < 2 ^ 32} :=
  exportAcceptedNotRejected_eq nohost_mem_allHosts

theorem allHosts_nonempty : allHosts.Nonempty := ⟨_, nohost_mem_allHosts⟩

theorem emptyCheck_checkAccept : checkAccept Silmaril.Wasm.Examples.EmptyCheck.prog = ∅ :=
  Silmaril.Wasm.Examples.EmptyCheck.exportAccepted_eq_empty _ _

theorem emptyCheck_checkReject :
    checkReject Silmaril.Wasm.Examples.EmptyCheck.prog = {w | w.length < 2 ^ 32} :=
  Silmaril.Wasm.Examples.EmptyCheck.exportRejected_eq _ allHosts_nonempty

theorem memberCheck_checkAccept_subset :
    checkAccept Silmaril.Wasm.Examples.MemberCheck.prog ⊆
      Silmaril.Wasm.Examples.MemberCheck.memberLang :=
  Silmaril.Wasm.Examples.MemberCheck.exportAccepted_subset _ _

theorem memberCheck_checkAccept : checkAccept Silmaril.Wasm.Examples.MemberCheck.prog =
    {w | w ∈ Silmaril.Wasm.Examples.MemberCheck.memberLang ∧ w.length < 2 ^ 32} :=
  Silmaril.Wasm.Examples.MemberCheck.exportAccepted_eq _ allHosts_nonempty

theorem memberCheck_checkReject : checkReject Silmaril.Wasm.Examples.MemberCheck.prog =
    {w | w ∉ Silmaril.Wasm.Examples.MemberCheck.memberLang ∧ w.length < 2 ^ 32} :=
  Silmaril.Wasm.Examples.MemberCheck.exportRejected_eq _ allHosts_nonempty

end Silmaril.Project.Languages.WasmExport
