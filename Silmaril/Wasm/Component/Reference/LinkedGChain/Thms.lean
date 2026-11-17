module

public import Silmaril.Wasm.Component.Reference.LinkedGChain.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInst.Thms
public import Silmaril.Wasm.Component.Reference.LinkedG.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Main

/-!
# Chains of linked components on the reference side: theorems

**Scope.** Every profile `P` and component choice profile; the reference machine over `core3P P`
under `linkHost impl`; chains built on an exporter meeting `RefAdeqUX` (in particular a simple
exporter, `Simple.expSpec_refAdeqU`) with links meeting `LinkedG.LinkOk`; typed calls.

**Proved, conditionally on the open goal** `Task.linkedG.toExpRefAdeqUX` (`Defs`: a linked
component, as an exporter at its importer's core instance, meets `RefAdeqUX`), by induction
along the chain:

* `chainExp_refAdeqUX_of`: the chain built on an exporter meeting `RefAdeqUX` meets `RefAdeqUX`;
* `chain_sessObs_eq_of`, `chain_sessAdequacy_of`: one more importer linked onto such a chain has
  reference session observations equal to its specification sessions (`LinkedG.sessObs_eqUX`)
  and to the reference images of its IR session plays (`LinkedG.sessAdequacy_fullUX`, the IR
  interface of the chain from `chainExp_adeq`);
* `LinkedN.sessAdequacy_full_of`: **finite session adequacy of a chain**: for the chain `n` with
  a simple base and one more importer `b` (`LinkedN.mk n.base (n.links ++ [(b, w)])`), reference
  session outcomes are exactly the specification sessions and exactly the reference images of
  the session plays of its IR component (`LinkedN.toComp_extend`).

**Proved unconditionally.** `ChainOkR.chainOk` (the reference hypotheses of a chain give
`ChainOk`), `LinkedN.toComp_extend`.

**Not claimed.** `Task.linkedG.toExpRefAdeqUX` itself (see `Defs`). What it needs, beyond the
theorems of `LinkedGRound`/`LinkedGInv`/`LinkedGInst` (whose rounds start from the host's
invocation between calls):

* a `Hold` for the linked exporter combining the exporter's `Hold`, `LReadyG` of the importer
  (whose footprint is the image of its ownership) and the importer's frame facts (`FrameG`'s
  `mayLeave`, the export instances reusable). R1 (`Frame.agree`) lets the functions grow, and
  `LReadyG`/`StatB` fix the shared functions `F₀` and a host-code renaming inverted on all of
  them; so this `Hold` must choose the renaming existentially and re-choose it on the grown
  functions (agreeing on the old ones), as `gX`/`trX` do at instantiation;
* R2/R3 in any frame from the importer's core activation: `rounds_fwdB` and the read-back of
  `LinkedGInv` already run from `coreCfg M th K segs rest` in any frame, but their ends
  (`RoundEndB`, `TrapAtG`) do not record that the core store changed only inside the combined
  footprint (`CoreFoot.Within`, `Grows`), which R2/R3's ends require;
* R4 as `InitUX` from any configuration with an empty core store: `instG_lrun` runs from
  `initConfig` after the host's instantiation event.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **The reference hypotheses of a chain give the IR ones** (proved). -/
theorem ChainOkR.chainOk {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (h : ChainOkR e bs Is) : ChainOk e bs Is :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chainOkR_chainOk e bs Is h

/-- **Chains of reference exporters** (proved, conditionally on the open goal): the chain built
on an exporter meeting `RefAdeqUX` meets `RefAdeqUX`. -/
theorem chainExp_refAdeqUX_of (hT : Task.linkedG.toExpRefAdeqUX) (P : Profile) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (he : e.RefAdeqUX P)
    (h : ChainOkR e bs Is) : (chainExp e bs Is).RefAdeqUX P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chainExp_refAdeqUX hT P e bs Is he h

/-- **Reference sessions of one more importer on a chain are specification sessions** (proved,
conditionally on the open goal; every profile and component choice profile, typed calls). -/
theorem chain_sessObs_eq_of (hT : Task.linkedG.toExpRefAdeqUX) (P : Profile)
    (prof : ProfileKind) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.RefAdeqUX P) (h : ChainOkR e bs Is) {b : SimpleI}
    {w : List Nat} (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin b.exports.length × List IVal))
    (ht : SimpleI.TypedCalls b calls) {Ii : ScalarInstance} (hI : b.mod.IsInst Ii) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : (chainExp e bs Is).St),
        LinkedG.SessSpec P ⟨chainExp e bs Is, b, w⟩ Ii Ii.store (chainExp e bs Is).init calls
          outs u' s' ∧ o = refOuts outs} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chain_sessObs_eq hT P prof he h hl impl
    h₀ calls ht hI

/-- **Finite session adequacy of one more importer on a chain** (proved, conditionally on the
open goal; every profile and component choice profile, typed calls): for a chain built on an
exporter meeting `RefAdeqUX` and `Adeq`, the session observations are the reference images of
the outcome lists whose session play is a play of the link's IR component. -/
theorem chain_sessAdequacy_of (hT : Task.linkedG.toExpRefAdeqUX) (P : Profile)
    (prof : ProfileKind) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.RefAdeqUX P) (hA : e.Adeq P) (h : ChainOkR e bs Is)
    {b : SimpleI} {w : List Nat} (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin b.exports.length × List IVal))
    (ht : SimpleI.TypedCalls b calls) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        (LinkedG.mk (chainExp e bs Is) b w).sessMoves calls outs ∈
          (LinkedG.mk (chainExp e bs Is) b w).toComp.den (impSem P)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chain_sessAdequacy hT P prof he hA h hl
    impl h₀ calls ht

namespace LinkedN

/-- **The IR component of a chain with one more importer** is that of the importer linked onto
the chain's specification (proved). -/
theorem toComp_extend {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) (b : SimpleI) (w : List Nat) :
    (LinkedG.mk (n.spec Ib Is) b w).toComp = (LinkedN.mk n.base (n.links ++ [(b, w)])).toComp :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.toComp_extend h b w

/-- **Finite session adequacy of a chain** (proved, conditionally on the open goal; every
profile and component choice profile, typed calls): for the chain `n` (simple base under the
hypotheses of `Simple.expSpec_refAdeqU`, links meeting `ChainOkR`) with one more importer `b`
meeting `LinkOk`, the reference session observations are exactly the specification sessions,
and exactly the reference images of the outcome lists whose session play is a play of the IR
component (`toComp_extend`: the IR component of `LinkedN.mk n.base (n.links ++ [(b, w)])`). -/
theorem sessAdequacy_full_of (hT : Task.linkedG.toExpRefAdeqUX) (P : Profile)
    (prof : ProfileKind) {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}
    (hb : n.base.Good) (hbi : n.base.Inst) (hIb : n.base.mod.IsInst Ib)
    (hbS : Linked2.ModSplitOk n.base.mod.mod) (hbN : ∀ x ∈ n.base.exports, ∀ m, x.name ≠ tag "t" m)
    (h : ChainOkR (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (n.spec Ib Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (ht : SimpleI.TypedCalls b calls)
    {Ii : ScalarInstance} (hI : b.mod.IsInst Ii) :
    LinkedG.sessObs prof ⟨n.spec Ib Is, b, w⟩ impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : (n.spec Ib Is).St),
        LinkedG.SessSpec P ⟨n.spec Ib Is, b, w⟩ Ii Ii.store (n.spec Ib Is).init calls outs u' s' ∧
          o = refOuts outs} ∧
    LinkedG.sessObs prof ⟨n.spec Ib Is, b, w⟩ impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        (LinkedG.mk (n.spec Ib Is) b w).sessMoves calls outs ∈
          (LinkedG.mk (n.spec Ib Is) b w).toComp.den (impSem P)} :=
  ⟨chain_sessObs_eq_of hT P prof (Simple.expSpec_refAdeqU P hb hbi hIb hbS hbN).refAdeqUX h hl
      impl h₀ calls ht hI,
    chain_sessAdequacy_of hT P prof (Simple.expSpec_refAdeqU P hb hbi hIb hbS hbN).refAdeqUX
      (Simple.expSpec_adeq P hb hIb) h hl impl h₀ calls ht⟩

end LinkedN

end Silmaril.Wasm.Component.Reference
