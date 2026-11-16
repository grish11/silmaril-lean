module

public import Silmaril.Project.Languages.WasmExport.Defs
public import Silmaril.Wasm.Examples.JsonAccept.Exact.Thms

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

end Silmaril.Project.Languages.WasmExport
