module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Agree
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Bwd
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Init

/-!
# A linked component is a reference exporter

`toExp_refAdeqUX`: for an exporter meeting `ExpSpec.RefAdeqUX` (data `d`) and a link meeting
`LinkedG.LinkOk`, the linked component at an instance `Ii` of its importer's core module meets
`RefAdeqUX`, with the data `toExpData lg d Ii` of `Data`: R1 (`Agree`), R2 (`Fwd`), R3 as `BwdF`
(`Bwd`), R4 as `InitUX` (`Init`), R5 and R6 (`Data`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

/-- **A linked component is a reference exporter.** -/
theorem toExp_refAdeqUX (P : Profile) (lg : LinkedG) (Ii : ScalarInstance)
    (he : lg.exp.RefAdeqUX P) (hl : lg.LinkOk) (hI : lg.imp.mod.IsInst Ii) :
    (lg.toExp Ii).RefAdeqUX P :=
  let ⟨d, hFr, hFw, hBw, hInit, hRes, hB⟩ := he
  ⟨toExpData lg d Ii, toExpData_frame hFr, toExpData_fwd hFr hFw hRes hB,
    toExpData_bwdF hFr hBw hRes hB, toExpData_initUX hInit hFr hB hl hI, toExpData_resume hRes,
    toExpData_bounded⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
