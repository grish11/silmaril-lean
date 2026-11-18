module

public import Silmaril.Wasm.Component.Reference.LinkedGChain.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInst.Thms
public import Silmaril.Wasm.Component.Reference.LinkedG.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Exp

/-!
# Chains of linked components on the reference side, from the open goal

* `chainOkR_chainOk`: the reference hypotheses of a chain give the IR ones (`ChainOk`);
* `chainExp_refAdeqUX`: by induction along the chain, with `toExp_refAdeqUX` (`Exp`) at each
  link, the chain built on an exporter meeting `RefAdeqUX` meets `RefAdeqUX`;
* `chain_sessObs_eq`, `chain_sessAdequacy`: one more importer linked onto such a chain has
  `LinkedG.sessObs_eqUX` and `LinkedG.sessAdequacy_fullUX`, the IR interface of the chain from
  `chainExp_adeq` (`LinkedG.toExp_adeq` at each link);
* `chainComp_append`, `toComp_extend`: the IR component of the extended link is the IR
  component of the extended chain.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

theorem chainOkR_chainOk :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance),
      ChainOkR e bs Is → ChainOk e bs Is
  | _, [], [], _ => trivial
  | e, (b, w) :: bs, I :: Is, ⟨hl, hI, h⟩ =>
    ⟨hl.good, hI, hl.wireTy, chainOkR_chainOk (LinkedG.toExp ⟨e, b, w⟩ I) bs Is h⟩
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

theorem chainExp_refAdeqUX (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance),
      e.RefAdeqUX P → ChainOkR e bs Is → (chainExp e bs Is).RefAdeqUX P
  | _, [], [], he, _ => he
  | e, (b, w) :: bs, I :: Is, he, ⟨hl, hI, h⟩ =>
    chainExp_refAdeqUX P (LinkedG.toExp ⟨e, b, w⟩ I) bs Is (toExp_refAdeqUX P ⟨e, b, w⟩ I he hl hI)
      h
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

variable {e : ExpSpec} {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance}

theorem chain_sessObs_eq (P : Profile) (prof : ProfileKind)
    (he : e.RefAdeqUX P) (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (ht : SimpleI.TypedCalls b calls)
    {Ii : ScalarInstance} (hI : b.mod.IsInst Ii) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : (chainExp e bs Is).St),
        LinkedG.SessSpec P ⟨chainExp e bs Is, b, w⟩ Ii Ii.store (chainExp e bs Is).init calls
          outs u' s' ∧ o = refOuts outs} :=
  LinkedG.sessObs_eqUX P prof (chainExp_refAdeqUX P e bs Is he h) hl.wireTy hl.nodup hl.good
    hl.inst hl.arity hl.floats hl.split hl.names impl h₀ calls ht hI

theorem chain_sessAdequacy (P : Profile) (prof : ProfileKind)
    (he : e.RefAdeqUX P) (hA : e.Adeq P) (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal))
    (ht : SimpleI.TypedCalls b calls) :
    LinkedG.sessObs prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        (LinkedG.mk (chainExp e bs Is) b w).sessMoves calls outs ∈
          (LinkedG.mk (chainExp e bs Is) b w).toComp.den (impSem P)} :=
  LinkedG.sessAdequacy_fullUX P prof (chainExp_refAdeqUX P e bs Is he h)
    (chainExp_adeq P hA (chainOkR_chainOk e bs Is h)) hl.wireTy hl.nodup hl.good hl.inst
    hl.arity hl.floats hl.split hl.names impl h₀ calls ht

theorem chainComp_append (b : SimpleI) (w : List Nat) :
    ∀ (A : Comp ImpModule) (bs : List (SimpleI × List Nat)),
      chainComp A (bs ++ [(b, w)]) = linkComp (chainComp A bs) b w
  | _, [] => rfl
  | A, (b', w') :: bs => chainComp_append b w (linkComp A b' w') bs

/-- The IR component of the chain `n` with one more importer `b` is the IR component of the link
of `b` onto the chain's specification. -/
theorem toComp_extend {n : LinkedN} {Ib : ScalarInstance}
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) (b : SimpleI) (w : List Nat) :
    (LinkedG.mk (n.spec Ib Is) b w).toComp = (LinkedN.mk n.base (n.links ++ [(b, w)])).toComp := by
  show linkComp (n.spec Ib Is).comp b w = chainComp _ (n.links ++ [(b, w)])
  rw [LinkedN.spec_comp h, chainComp_append]
  rfl

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
