module

public import Silmaril.Wasm.Component.DecoderBridge.Named.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Wasm.Component.DecoderBridge.ParamName.Defs
public import Silmaril.Wasm.Component.DecoderBridge.InstExport.Defs
public import Silmaril.Wasm.Component.InstTests.Defs
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.Main

/-!
# The two readings with parameter names (theorems)

All proved; proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Named`.

## The named IR reading

* `parseComponentN_ok`, `parseComponentN_of_ok`: the named IR reading `Binary.parseComponentN`
  succeeds exactly when `Binary.parseComponent` does, with the same IR component (`n.comp`);
* `named_of_decode`: **for every binary** whose readings succeed and whose reference reading has
  a named reading (`refReadN r = some N`), the named IR imports and exports are those of the
  reference reading, parameter names included;
* `refReadN_of_inFrag`, `erase_of_decode`: on the fragment `InFrag` the named reading exists, and
  erasing the parameter names gives the IR's imports and exports (`Comp.imports`,
  `Comp.exports`): the named reading refines the IR reading.

## The start goal on the named IR

* `rootChecked_of_named`: on `InFrag`, the **IR's own import typing** `n.imports = hostIN` gives
  the root compatibility certificate `RootChecked`; `hostI_of_named`: and `c.imports = hostI`;
* `startAdequacyNamed_of_checked`: `Task.startAdequacyChecked → Task.startAdequacyNamed`: the
  start goal on the named IR needs no certificate;
* `startAdequacyNamed_of_multiImpFrag`: its conclusion on `MultiImpFrag`, proved;
* `parseN_paramName`, `paramName_not_hostIN`: the named IR reading of `paramname.wasm` imports
  `f: func(y: u32)`, not `hostIN`, so **`paramname.wasm` is not a counterexample** to
  `Task.startAdequacyNamed` (it refutes `Task.startAdequacy`, `ParamName.not_startAdequacy`,
  where the IR reading drops the name);
* `parseN_starts`: `starts.wasm` imports `hostIN` and meets the hypotheses.

## Exported instances: the restriction

* `inFrag_noInstExport`: `InFrag r → NoInstExport r`;
* `exportNames_of_decode`: **for every binary** whose readings succeed and whose reference reading
  exports no instance (`NoInstExport`, decidable), the named IR export names are the reference
  reading's function export names (`refFuncExportNames`), in order; `exportNames_ir_of_inFrag`:
  on `InFrag`, so are the IR's (`Comp.exports`);
* `instExport_not_noInstExport`, `parseN_instExport`, `instExport_names`: `instexport.wasm` is
  outside the restriction, and there the names differ (`i#get` against none). The mismatch is
  not resolved: the IR still flattens exported instances.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Binary (NComp NSig NIface parseComponentN)
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **The named IR reading succeeds with the IR reading's component.** -/
theorem parseComponentN_ok {b : ByteArray} {n : NComp} (h : parseComponentN b = .ok n) :
    Binary.parseComponent b = .ok n.comp :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.parseComponentN_ok h

/-- **The named IR reading succeeds whenever the IR reading does.** -/
theorem parseComponentN_of_ok {b : ByteArray} {c : Comp Binary.CoreMod}
    (h : Binary.parseComponent b = .ok c) : ∃ n, parseComponentN b = .ok n ∧ n.comp = c :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.parseComponentN_of_ok h

/-- **The named IR signature is the named reference reading.** -/
theorem named_of_decode {b : ByteArray} {n : NComp} {r : RefComponent} {N : RN}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hN : refReadN r = some N) :
    n.imports = N.imports ∧ n.exports = N.exports :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.named_of_decode hc hr hN

/-- On the fragment the named reference reading exists. -/
theorem refReadN_of_inFrag {r : RefComponent} (h : InFrag r) : ∃ N, refReadN r = some N :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.refReadN_of_inFrag h

/-- **On the fragment the named IR erases to the IR.** -/
theorem erase_of_decode {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    NIface.erase n.imports = n.comp.imports ∧
      n.exports.map (fun p => (p.1, p.2.erase)) = n.comp.exports.map fun e => (e.name, e.ty) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.erase_of_decode hc hr hf

/-- **The IR's named import typing gives the root certificate.** -/
theorem rootChecked_of_named {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r)
    (hi : n.imports = hostIN) : RootChecked r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.rootChecked_of_named hc hr hf hi

/-- The named import typing erases to `hostI`. -/
theorem hostI_of_named {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r)
    (hi : n.imports = hostIN) : n.comp.imports = hostI :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.hostI_of_named hc hr hf hi

/-- **The start goal on the named IR from the corrected start goal.** -/
theorem startAdequacyNamed_of_checked (h : Task.startAdequacyChecked) : Task.startAdequacyNamed :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.startAdequacyNamed_of_checked h

/-- **The start goal on the named IR, on `MultiImpFrag`, proved.** -/
theorem startAdequacyNamed_of_multiImpFrag (b : ByteArray) (n : NComp) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (nm : String)
    (ws : List Silmaril.Wasm.Component.Val)
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r)
    (hv : ∃ ct, Valid Features.p2 r ct) (hf : InFrag r) (hm : MultiImpFrag r)
    (hi : n.imports = hostIN) (hex : (n.comp.exports.map (·.name)).head? = some nm)
    (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hp : instPlay (F := sigU) t .ready ++
      [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
        n.comp.denI (Binary.coreModSemI (profile neverFail))) :
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(nm, [])] :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.startAdequacyNamed_of_multiImpFrag
    b n r t nm ws hc hr hv hf hm hi hex hu hp

/-- **The named IR reading of `paramname.wasm`**: the IR component of `starts.wasm`, importing
`f: func(y: u32)`. -/
theorem parseN_paramName :
    parseComponentN paramNameBytes =
      .ok ⟨startsComp, ⟨[("f", ⟨[("y", .u32)], []⟩)], [("get", ⟨[], [.u32]⟩)]⟩⟩ :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.parseN_paramName

/-- **`paramname.wasm` is not a counterexample to `Task.startAdequacyNamed`**: its named import
is not `hostIN`. -/
theorem paramName_not_hostIN {n : NComp} (h : parseComponentN paramNameBytes = .ok n) :
    n.imports ≠ hostIN := by
  rw [parseN_paramName] at h
  cases h
  decide

/-- **The named IR reading of `starts.wasm`**: it imports `hostIN`. -/
theorem parseN_starts :
    parseComponentN startsBytes = .ok ⟨startsComp, ⟨hostIN, [("get", ⟨[], [.u32]⟩)]⟩⟩ :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.parseN_starts

/-- The fragment exports no instance. -/
theorem inFrag_noInstExport {r : RefComponent} (h : InFrag r) : NoInstExport r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.inFrag_noInstExport h

/-- **Without exported instances, the named IR exports the reference's function exports, by
name**, for every binary. -/
theorem exportNames_of_decode {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hn : NoInstExport r) :
    n.exports.map (·.1) = refFuncExportNames r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.exportNames_of_decode hc hr hn

/-- On the fragment, so does the IR. -/
theorem exportNames_ir_of_inFrag {b : ByteArray} {n : NComp} {r : RefComponent}
    (hc : parseComponentN b = .ok n) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    n.comp.exports.map (·.name) = refFuncExportNames r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.exportNames_ir_of_inFrag hc hr hf

/-- **`instexport.wasm` is outside the restriction.** -/
theorem instExport_not_noInstExport : ¬ NoInstExport instExportRef := by decide +kernel

/-- **The named IR reading of `instexport.wasm`**: one export, named `i#get`. -/
theorem parseN_instExport :
    parseComponentN instExportBytes =
      .ok ⟨instExportComp, ⟨hostIN, [("i#get", ⟨[], [.u32]⟩)]⟩⟩ :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Named.parseN_instExport

/-- **There the export names differ**: `i#get` in the IR, no function export in the reference
reading. -/
theorem instExport_names :
    refFuncExportNames instExportRef = [] ∧ instExportComp.exports.map (·.name) = ["i#get"] :=
  ⟨by decide +kernel, rfl⟩

end Silmaril.Wasm.Component.DecoderBridge
