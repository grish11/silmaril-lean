module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Exp
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Simple
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.SimpleIR
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Main

/-!
# Divergence through an abstract exporter: assembly

* `sessDivs_eq_refDivsG`: for an exporter meeting `RefAdeqUXD` and a link meeting `LinkOk`, the
  diverging session calls of the specification are those of the reference machine
  (`divSpecToRefG`, `divRefToSpecG`);
* `chainExp_refAdeqUXD`: by induction along a chain, from `toExp_refAdeqUXD`;
* `chain_sessDivs_eq_refDivs`: one more importer linked onto such a chain.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- `RefAdeqUXD` implies `RefAdeqUX`. -/
theorem refAdeqUXD_refAdeqUX {P : Profile} {e : ExpSpec} (h : e.RefAdeqUXD P) : e.RefAdeqUX P :=
  let ⟨d, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := h
  ⟨d, h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- `divSpecToRefG` for an exporter meeting `RefAdeqUXD` and a link meeting `LinkOk`. -/
theorem divSpecToRefD (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessDivs P lg Ii calls j vs ⊆ LinkedG.refDivs P prof lg impl h₀ calls j vs :=
  let ⟨_, hFr, hFw, _, hInit, hRes, hB, hDv⟩ := he
  divSpecToRefG P prof (LinkedGInst.initUX_initSX hInit) hFr hFw hRes hB hDv hl.wireTy
    hl.nodup hl.good hl.inst hl.arity hl.floats hl.split hl.names impl h₀ calls j vs hI

/-- `divRefToSpecG` for an exporter meeting `RefAdeqUXD` and a link meeting `LinkOk`. -/
theorem divRefToSpecD (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls lg.imp calls)
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.refDivs P prof lg impl h₀ calls j vs ⊆ LinkedG.sessDivs P lg Ii calls j vs :=
  let ⟨_, hFr, _, hBw, hInit, hRes, hB, hDv⟩ := he
  divRefToSpecG P prof hInit hFr hBw hRes hB hDv hl.wireTy hl.nodup hl.good hl.inst hl.arity
    hl.floats hl.split hl.names impl h₀ calls j vs ht hvs hI

/-- **The diverging session calls of a linked component with an abstract exporter.** -/
theorem sessDivs_eq_refDivsG (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls lg.imp calls)
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessDivs P lg Ii calls j vs = LinkedG.refDivs P prof lg impl h₀ calls j vs :=
  Set.Subset.antisymm (divSpecToRefD P prof he hl impl h₀ calls j vs hI)
    (divRefToSpecD P prof he hl impl h₀ calls j vs ht hvs hI)

/-- **Chains of reference exporters with divergence.** -/
theorem chainExp_refAdeqUXD (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance),
      e.RefAdeqUXD P → ChainOkR e bs Is → (chainExp e bs Is).RefAdeqUXD P
  | _, [], [], he, _ => he
  | e, (b, w) :: bs, I :: Is, he, ⟨hl, hI, h⟩ =>
    chainExp_refAdeqUXD P (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
      (toExp_refAdeqUXD P ⟨e, b, w⟩ I he hl hI) h
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

/-- **The diverging session calls of one more importer on a chain.** -/
theorem chain_sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (he : e.RefAdeqUXD P)
    (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (j : Fin b.exports.length)
    (vs : List IVal) (ht : SimpleI.TypedCalls b calls)
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : b.mod.IsInst Ii) :
    LinkedG.sessDivs P ⟨chainExp e bs Is, b, w⟩ Ii calls j vs =
      LinkedG.refDivs P prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls j vs :=
  sessDivs_eq_refDivsG P prof (chainExp_refAdeqUXD P e bs Is he h) hl impl h₀ calls j vs ht hvs hI

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv
