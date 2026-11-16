module

public import Silmaril.Wasm.Game.Accept.Export.Defs
public import Silmaril.Semantics.Accept.Verdict.Thms

/-! # The export embedding as a generic acceptor

The readings of `Silmaril.Wasm.Game.Accept.Export` are the generic ones of
`Silmaril.Semantics.Accept` for **one** runner, `exportRun` (the results of the embedding's runs
on an input), with accepting result `1` and rejecting result `0`:

* `exportAccepted_eq_acceptsSome`, `exportRejected_eq_rejectsSome`;
* `exportAcceptedNotRejected_eq_acceptsSafely`: the combined reading is
  `Silmaril.Accept.acceptsSafely` (#296): some run accepts and no run rejects, over the same
  runs and the same hosts.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {P : Profile} {Hosts : Set (HostSemantics Nat)} {m : Module} {name : String}

theorem exportAccepted_eq_acceptsSome :
    exportAccepted P Hosts m name = Silmaril.Accept.acceptsSome (exportRun P Hosts m name) {1} := by
  ext w; simp [exportAccepted, exportRun, Silmaril.Accept.acceptsSome]

theorem exportRejected_eq_rejectsSome :
    exportRejected P Hosts m name = Silmaril.Accept.rejectsSome (exportRun P Hosts m name) {0} := by
  ext w; simp [exportRejected, exportRun, Silmaril.Accept.rejectsSome]

/-- **Accepted and never rejected is `acceptsSafely` of one runner.** -/
theorem exportAcceptedNotRejected_eq_acceptsSafely :
    exportAcceptedNotRejected P Hosts m name =
      Silmaril.Accept.acceptsSafely (exportRun P Hosts m name) {1} {0} := by
  ext w
  simp [exportAcceptedNotRejected, exportAccepted, exportRejected, exportRun,
    Silmaril.Accept.acceptsSafely, Silmaril.Accept.acceptsSome, Silmaril.Accept.neverRejects]
  exact fun _ => ⟨fun h o ho h0 => h (h0 ▸ ho), fun h h0 => h 0 h0 rfl⟩

end Silmaril.Wasm.Game.Accept
