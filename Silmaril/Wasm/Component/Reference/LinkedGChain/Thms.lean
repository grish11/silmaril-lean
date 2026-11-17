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

**Proved (public, below).**

* `LinkedG.toExp_refAdeqUX`: **a linked component is a reference exporter**: for an exporter
  meeting `RefAdeqUX` and a link meeting `LinkOk`, the linked component at an instance `Ii` of
  its importer's core module (`LinkedG.toExp`) meets `RefAdeqUX` (R1, R2, R3 as `BwdF`, R4 as
  `InitUX`, R5, R6), with the interface unchanged;
* `chainExp_refAdeqUX`: by induction along the chain, the chain built on an exporter meeting
  `RefAdeqUX` meets `RefAdeqUX`;
* `chain_sessObs_eq`, `chain_sessAdequacy`: one more importer linked onto such a chain has
  reference session observations equal to its specification sessions (`LinkedG.sessObs_eqUX`)
  and to the reference images of its IR session plays (`LinkedG.sessAdequacy_fullUX`, the IR
  interface of the chain from `chainExp_adeq`);
* `LinkedN.sessAdequacy_full`: **finite session adequacy of a chain**: for the chain `n` with
  a simple base and one more importer `b` (`LinkedN.mk n.base (n.links ++ [(b, w)])`), reference
  session outcomes are exactly the specification sessions and exactly the reference images of
  the session plays of its IR component (`LinkedN.toComp_extend`);
* `ChainOkR.chainOk` (the reference hypotheses of a chain give `ChainOk`),
  `LinkedN.toComp_extend`.

**Proved (proof-internal, in `Proofs.….LinkedGChain`): the reference data of a linked
component** (`Data`: `toExpData lg d Ii` from the exporter's data `d`).

* **Placement and relation** (`ExpPl`, `HoldX`): the exporter's placement, the importer's
  instance, relocation, store after instantiation, ownership and first export function id; the
  relation combines the importer's static facts `StatB`, its invariant between calls at an
  explicit witness (`LReadyW`), the importer's instance allowed to leave, the export instances
  reusable, and a footprint `Fc` that contains the exporter's footprint and the image of the
  importer's ownership and is allocated. The host-code renaming `(g, tr)` and the shared
  functions `F₀` are existential.
* **R1** (`Agree`): `F₀` grows; the renaming is re-chosen on the grown functions (`gRe`,
  `trRe`), agreeing with the old one on the old host code and the importer's trampolines, the
  new host code sent above every old value.
* **R2** (`Fwd`), **R3** (`Bwd`): the rounds of `LinkedGRound`/`LinkedGInv` with the footprint
  tracked (`Track`: `RelT`, `TrapT`, `rounds_fwdT`; `Back`: `phase_backT`, which also records the
  run up to the importer's exit), from any frame; changes since the start lie in `Fc` and fresh
  addresses (`CoreFoot.Within`), and the end's footprint is `Fc` with the newly allocated
  structs and arrays (`growFoot`, `CoreFoot.Grows`). `call_stepB'`, `call_backB'`
  (`LinkedGRound`, `LinkedGInv`, generalised in place) expose the exporter's end.
* **R4** (`InitRun`, `Init`): the stages of `LinkedGInst.Run` at any instance, outer frames and
  thread (`toRefG_reacho`), and a late-bound call by a live run (`ReachL.callL`), so the nested
  instantiation of `lg.toRef` from any configuration with an empty core store is a live run
  (`instCallG_reach`), where `HoldX` holds (`statB_init`, the invariant of `readyB_init`).
* **R5, R6** (`Data`): from the exporter's R5; the footprint is allocated by definition.

**Deviations.** None in the interface: `RefAdeqUX` is met as stated, so no field had to be
corrected and `Simple` is unaffected. The linked component's footprint is any allocated
footprint containing the combined one (not exactly it), so that R2/R3 can end at the starting
footprint grown by the fresh addresses.

**Not claimed.** Divergence and infinite plays of chains; general `ext`/nested `.inst`
components beyond `LinkedN`; ill-typed calls.
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

/-- **A linked component is a reference exporter** (proved, every profile): for an exporter
meeting `RefAdeqUX` and a link meeting `LinkOk`, the linked component at an instance `Ii` of its
importer's core module meets `RefAdeqUX`. -/
theorem LinkedG.toExp_refAdeqUX (P : Profile) {lg : LinkedG} {Ii : ScalarInstance}
    (he : lg.exp.RefAdeqUX P) (hl : lg.LinkOk) (hI : lg.imp.mod.IsInst Ii) :
    (lg.toExp Ii).RefAdeqUX P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.toExp_refAdeqUX P lg Ii he hl hI

/-- **Chains of reference exporters** (proved): the chain built on an exporter meeting
`RefAdeqUX` meets `RefAdeqUX`. -/
theorem chainExp_refAdeqUX (P : Profile) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.RefAdeqUX P) (h : ChainOkR e bs Is) :
    (chainExp e bs Is).RefAdeqUX P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chainExp_refAdeqUX P e bs Is he h

/-- **Reference sessions of one more importer on a chain are specification sessions** (proved,
every profile and component choice profile, typed calls). -/
theorem chain_sessObs_eq (P : Profile) (prof : ProfileKind) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (he : e.RefAdeqUX P)
    (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (ht : SimpleI.TypedCalls b calls)
    {Ii : ScalarInstance} (hI : b.mod.IsInst Ii) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : (chainExp e bs Is).St),
        LinkedG.SessSpec P ⟨chainExp e bs Is, b, w⟩ Ii Ii.store (chainExp e bs Is).init calls
          outs u' s' ∧ o = refOuts outs} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chain_sessObs_eq P prof he h hl impl
    h₀ calls ht hI

/-- **Finite session adequacy of one more importer on a chain** (proved, every profile and
component choice profile, typed calls): for a chain built on an exporter meeting `RefAdeqUX` and
`Adeq`, the session observations are the reference images of the outcome lists whose session
play is a play of the link's IR component. -/
theorem chain_sessAdequacy (P : Profile) (prof : ProfileKind) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (he : e.RefAdeqUX P)
    (hA : e.Adeq P) (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal))
    (ht : SimpleI.TypedCalls b calls) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        (LinkedG.mk (chainExp e bs Is) b w).sessMoves calls outs ∈
          (LinkedG.mk (chainExp e bs Is) b w).toComp.den (impSem P)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.chain_sessAdequacy P prof he hA h hl
    impl h₀ calls ht

namespace LinkedN

/-- **The IR component of a chain with one more importer** is that of the importer linked onto
the chain's specification (proved). -/
theorem toComp_extend {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) (b : SimpleI) (w : List Nat) :
    (LinkedG.mk (n.spec Ib Is) b w).toComp = (LinkedN.mk n.base (n.links ++ [(b, w)])).toComp :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.toComp_extend h b w

/-- **Finite session adequacy of a chain** (proved, every profile and component choice profile,
typed calls): for the chain `n` (simple base under the hypotheses of `Simple.expSpec_refAdeqU`,
links meeting `ChainOkR`) with one more importer `b` meeting `LinkOk`, the reference session
observations are exactly the specification sessions, and exactly the reference images of the
outcome lists whose session play is a play of the IR component (`toComp_extend`: the IR
component of `LinkedN.mk n.base (n.links ++ [(b, w)])`). -/
theorem sessAdequacy_full (P : Profile) (prof : ProfileKind) {n : LinkedN} {Ib : ScalarInstance}
    {Is : List ScalarInstance} (hb : n.base.Good) (hbi : n.base.Inst) (hIb : n.base.mod.IsInst Ib)
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
  ⟨chain_sessObs_eq P prof (Simple.expSpec_refAdeqU P hb hbi hIb hbS hbN).refAdeqUX h hl
      impl h₀ calls ht hI,
    chain_sessAdequacy P prof (Simple.expSpec_refAdeqU P hb hbi hIb hbS hbN).refAdeqUX
      (Simple.expSpec_adeq P hb hIb) h hl impl h₀ calls ht⟩

end LinkedN

end Silmaril.Wasm.Component.Reference
