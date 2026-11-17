module

public import Silmaril.Wasm.Component.Reference.LinkedGInit.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Simple

/-!
# The instantiation of a linked component with an abstract exporter: theorems

**Scope.** Every profile `P` and component choice profile; the reference machine over `core3P P`
under `linkHost impl` (any host state type and host functions); `LinkedG.toRef` with an exporter
meeting `ExpSpec.RefAdeqS` (`Defs`) and an importer as in `Linked2.Adequate`.

**Proved (public, below).**

* `ExpSpec.RefData.InitS.init`, `ExpSpec.RefAdeqS.refAdeqT`: `InitS` is R4 with more, so
  `RefAdeqS` is `RefAdeqT` of `LinkedGRound` with more.
* `Simple.expSpec_refAdeqS`: a simple exporter meets `RefAdeqS`, under the hypotheses of
  `Simple.expSpec_refAdeqT`.
* `LinkedG.sess_specToRefB`: **every `LinkedG.SessSpec` session from the importer's instance
  store and the exporter's initial state is a session behaviour of `lg.toRef`**
  (`refOuts outs ∈ LinkedG.sessObs …`), for a `RefAdeqS` exporter and an importer that is
  `Good`, `Inst`, within the flat arities, float-free, in the split fragment, with export names
  that are not generated type names, wired injectively (`wire.Nodup`) and well typed.
* `Linked2.sess_specToRef_viaG`: `Linked2.sess_specToRef` re-derived from
  `LinkedG.sess_specToRefB` at `Linked2.toG l Ie` with the simple exporter's data.

**Proved (proof-internal, in `Proofs.….LinkedGInit`).**

* `Reach`: a program in focus reaching a result in any context, with its observations; R4 as a
  `Reach` of the late-bound call `Call.instantiate` (`reach_initS`);
* `instG_run`: the instantiation of `lg.toRef` as a host event runs (the closures, R4, the
  aliases of the wired exports, the importer's nested instantiation over the shared store after
  R4's instances, functions and core store, the aliases of its exports and the exports) to
  `afterG`, observing the root instance `0` and the export map `exportMapG`;
* `statB_init`, `readyB_init`: `StatB` and `ReadyB` of `LinkedGRound` at `afterG`, call id `0`
  (the importer's trampolines `trG` and the host-code renaming `gG`; the exporter's `Hold`
  moved by R1 along the importer's instantiation; the importer's `Rel4` half from `rel4_init`,
  disjoint from the exporter's footprint).

**Deviation from the plan of `LinkedGRound`**: R4 (`RefData.Init`) does not determine enough of
the configuration after the exporter's instantiation for the parent's run and `ReadyB` (`Defs`:
observations, call records and nesting depth, host-free core store, footprint globals, distinct
function ids). The theorems use `InitS` (R4 with those facts) and `RefAdeqS`. The globals are
needed for any `RefAdeqT` exporter: from data meeting R1–R6, the data whose footprints are
`d`'s with every global added meets R1–R6 too (the argument of `ExpSpec.refAdeq_allStructs`;
R6 bounds only structs and arrays, and `Within`/`Grows` only weaken or keep the globals), and its
footprints are disjoint (`FootDisj`) from no importer ownership that owns a global, such as
`rel4_init`'s. The host code is needed by `StatB` as defined (`ImpStatG.tramp`: every host
function of the shared core store is an importer trampoline), which a linked exporter with its own
trampolines does not meet.

**Not claimed** (what remains):

* **The read-back** `LinkedG.linkCall_invB` against `BwdT`, `sess_refToSpec`, `sessObs_eq`, then
  `LinkedG.toExp_refAdeq` and `LinkedN.sessAdequacy_full`.
* **A bridge from `Linked2`'s `ReadyL`** (its `Rel4` under `gL`) to `LReadyG`: not needed for
  `Linked2.sess_specToRef_viaG`, which starts `LinkedG`'s sessions from its own instantiation.
* **Nested linked exporters**: `StatB` reads every host function of the shared core store as an
  importer trampoline; a chain needs `ImpStatG.tramp` restricted to the importer's functions.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **`InitS` implies R4** (proved). -/
theorem ExpSpec.RefData.InitS.init {P : Profile} {e : ExpSpec} {d : e.RefData P} (h : d.InitS) :
    d.Init :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.initS_init h

/-- **`RefAdeqS` implies `RefAdeqT`** (proved). -/
theorem ExpSpec.RefAdeqS.refAdeqT {P : Profile} {e : ExpSpec} (h : e.RefAdeqS P) :
    e.RefAdeqT P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.refAdeqS_refAdeqT h

/-- **A simple exporter meets `RefAdeqS`** (proved, every profile), under the hypotheses of
`Simple.expSpec_refAdeqT`. -/
theorem Simple.expSpec_refAdeqS (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (Simple.expSpec c I).RefAdeqS P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.simple_refAdeqS P hc hi hI hS hN

/-- **Specification sessions of a linked component with an abstract exporter are reference
sessions** (proved, every profile and component choice profile): the reference images of the
outcomes of every `LinkedG.SessSpec` session from the importer's instance store and the
exporter's initial state are session behaviours of `lg.toRef`. -/
theorem LinkedG.sess_specToRefB (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqS P) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin lg.imp.exports.length × List IVal)}
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {outs : List (Option (List IVal))} {u' : Silmaril.Wasm.Execution.Core.Store Nat}
    {s' : lg.exp.St} (hspec : LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s') :
    refOuts outs ∈ LinkedG.sessObs prof lg impl h₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.sess_specToRefS P prof he hW hn hIg hIi
    hIa hff hS hNI impl h₀ hI hspec

/-- **`Linked2.sess_specToRef` through `LinkedG`** (proved): the same statement, derived from
`LinkedG.sess_specToRefB` at `Linked2.toG l Ie`. -/
theorem Linked2.sess_specToRef_viaG (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List IVal)}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List IVal))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (hspec : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.linked2_sess_specToRefG P prof l hl impl h₀
    hIe hIi hspec

end Silmaril.Wasm.Component.Reference
