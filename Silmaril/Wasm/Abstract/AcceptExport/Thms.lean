module

public import Silmaril.Wasm.Abstract.AcceptExport.Defs
public import Silmaril.Wasm.Abstract.AcceptWasm.Thms
public import Silmaril.Wasm.Game.Accept.Export.Thms
import Silmaril.Proofs.Wasm.Abstract.AcceptExport

/-! # The export embedding through the abstract function semantics: theorems

The diagram commutes **exactly** for the actual instantiation embedding of
`Silmaril.Wasm.Game.Accept.Export`, with no assumed commuting field:

* `mem_exportAnswered_iff`: the embedding answers `r` on `w` iff some admitted call
  (`exportCalls`) with input `w` has the concrete behaviour `returns [i32 r]` (`behRun`, from its
  host-written store).
* `image_absExportRun`: the abstract endings map onto those concrete behaviours, for every input
  (from `endRun_wasmFun`, hence `image_wasmFun`).
* `exportRun_eq`: so the concrete runner `exportRun` is the abstract runner `absExportRun` read
  through `retI32`.
* **The three verdicts**, as generic verdicts of the abstract runner:
  * `exportAccepted_eq_abs`: `exportAccepted = acceptsSome absExportRun (retI32 1)`;
  * `exportRejected_eq_abs`: `exportRejected = rejectsSome absExportRun (retI32 0)`;
  * `exportAcceptedNotRejected_eq_abs`:
    `exportAcceptedNotRejected = acceptsSafely absExportRun (retI32 1) (retI32 0)`.
  Both quantifiers of the combined verdict range over the same abstract endings.
* `retAcceptsSafely_exportCall`: for one admitted call, the abstract function's own export
  reading (`retAcceptsSafely` of `wasmFun` from the call's store) on the call's arguments is the
  concrete one (`retAcceptsSafely_wasmFun`).

The proofs are in `Silmaril.Proofs.Wasm.Abstract.AcceptExport`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept Silmaril.Wasm.Abstract
open Silmaril.Games.Abstract

variable {P : Profile} {Hosts : Set (HostSemantics Nat)} {m : Module} {name : String}

/-- The embedding answers `r` iff some admitted call returns `i32 r`. -/
theorem mem_exportAnswered_iff {w : List UInt8} {r : BitVec 32} :
    w ∈ exportAnswered P Hosts m name r ↔ ∃ e ∈ exportCalls P Hosts m name, e.input = w ∧
      Behaviour.returns [.i32 r] ∈ behRun P e.host {e.store} e.addr e.args :=
  Silmaril.Proofs.Wasm.Abstract.AcceptExport.mem_exportAnswered_iff

/-- **The abstract endings map onto the concrete behaviours of the admitted calls.** -/
theorem image_absExportRun (w : List UInt8) :
    endToBehaviour '' absExportRun P Hosts m name w =
      {b | ∃ e ∈ exportCalls P Hosts m name, e.input = w ∧
        b ∈ behRun P e.host {e.store} e.addr e.args} :=
  Silmaril.Proofs.Wasm.Abstract.AcceptExport.image_absExportRun w

/-- **The concrete runner is the abstract runner read through `retI32`.** -/
theorem exportRun_eq (w : List UInt8) :
    exportRun P Hosts m name w = {r | ∃ x ∈ absExportRun P Hosts m name w, x ∈ retI32 r} :=
  Silmaril.Proofs.Wasm.Abstract.AcceptExport.exportRun_eq w

/-- **Acceptance commutes.** -/
theorem exportAccepted_eq_abs :
    exportAccepted P Hosts m name =
      Silmaril.Accept.acceptsSome (absExportRun P Hosts m name) (retI32 1) :=
  Set.ext fun _ => Silmaril.Proofs.Wasm.Abstract.AcceptExport.mem_acceptsSome_iff.symm

/-- **Rejection commutes.** -/
theorem exportRejected_eq_abs :
    exportRejected P Hosts m name =
      Silmaril.Accept.rejectsSome (absExportRun P Hosts m name) (retI32 0) :=
  Set.ext fun _ => Silmaril.Proofs.Wasm.Abstract.AcceptExport.mem_acceptsSome_iff.symm

/-- **The combined verdict commutes**, with one runner on each side. -/
theorem exportAcceptedNotRejected_eq_abs :
    exportAcceptedNotRejected P Hosts m name =
      Silmaril.Accept.acceptsSafely (absExportRun P Hosts m name) (retI32 1) (retI32 0) :=
  Set.ext fun _ => and_congr
    Silmaril.Proofs.Wasm.Abstract.AcceptExport.mem_acceptsSome_iff.symm
    Silmaril.Proofs.Wasm.Abstract.AcceptExport.mem_neverRejects_iff.symm

/-- For one admitted call, the abstract function's export reading is the concrete one. -/
theorem retAcceptsSafely_exportCall (e : ExportCall) (accB rejB : Set (Behaviour Val)) :
    e.args ∈ retAcceptsSafely (wasmFun P e.host e.addr) {e.store} (endToBehaviour ⁻¹' accB)
        (endToBehaviour ⁻¹' rejB) ↔
      e.args ∈ Silmaril.Accept.acceptsSafely (behRun P e.host {e.store} e.addr) accB rejB := by
  rw [retAcceptsSafely_wasmFun]

end Silmaril.Wasm.Abstract.Accept
