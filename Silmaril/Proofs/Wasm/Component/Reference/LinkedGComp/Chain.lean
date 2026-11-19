module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Thread
public import Silmaril.Wasm.Component.Reference.LinkedGLink.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Thms
public import Silmaril.Games.Abstract.SessionLink.Thms
public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Games.DivComp.Thms

/-!
# The canonical object of a link and of a chain as linked and composed sessions (proofs)

* `linkChain_mapStore`: the left-nested iterated link does not see a transport of its server's
  store (`linkS_mapStore_left`, `threadS_mapStore`);
* `session_chainExp_eq_linkChain`: the session object of a chain is the session of the
  left-nested iterated link, by induction from `compTripleS_eq_linkS`;
* `linkChain_cons_eq`: the left-nested iterated link has the session of the server linked with
  the right-nested link of the importers (`linkS_assoc`);
* `session_toExp_eq_comp`: one link is the composition of the exporter's and the importer's
  sessions (`SessionLink.comp_threadS`, with `RetDet` of both sides, preserved by linking, for the
  stores);
* `session_chainExp_eq_sessChain`, `sessChain_cons_eq`: chains, left- and right-nested
  (`DStrategy.comp_assoc`); `threadS_impStackT`: the right-nested link of the importers has the
  right-nested composition of their sessions as its session.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS comp_threadS)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore linkS_assoc)
open Silmaril.Games.Abstract.SessionLinkCoh (linkS_mapStore_left)
open Silmaril.Games.Abstract.StratSession (threadS NoPlainTrap)
open Silmaril.Games.Abstract.SessionCat (RetDet retDet_linkS storeDet_of_retDet)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink (compTripleS_eq_linkS)

/-! ## Linked triples, every profile -/

theorem linkChain_mapStore (P : Profile) :
    ∀ (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance) {S S' : Type} (σ : S ≃ S')
      (T : ObsTriple (sigN 0) S (Nat × Payload) (Payload ⊕ PUnit)) (s : S),
      linkChain P (mapStore σ T) (σ s) bs Is = linkChain P T s bs Is
  | [], _, _, _, σ, T, s => Silmaril.Wasm.Component.Reference.threadS_mapStore σ T s
  | (_, _) :: _, [], _, _, σ, T, s => Silmaril.Wasm.Component.Reference.threadS_mapStore σ T s
  | (b, w) :: bs, I :: Is, _, _, σ, T, s => by
    change linkChain P (linkS (mapStore σ T) (b.impTripleS P w I)) (σ s, I.store) bs Is =
      linkChain P (linkS T (b.impTripleS P w I)) (s, I.store) bs Is
    rw [linkS_mapStore_left]
    exact linkChain_mapStore P bs Is (Equiv.prodCongr σ (Equiv.refl _)) _ (s, I.store)

theorem session_chainExp_eq_linkChain (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance),
      ChainWire e bs Is → (chainExp e bs Is).session P = linkChain P (e.sessTripleS P) e.init bs Is
  | _, [], _, _ => rfl
  | _, (_, _) :: _, [], _ => rfl
  | e, (b, w) :: bs, I :: Is, h => by
    change (chainExp (LinkedG.toExp ⟨e, b, w⟩ I) bs Is).session P =
      linkChain P (linkS (e.sessTripleS P) (b.impTripleS P w I)) (e.init, I.store) bs Is
    rw [session_chainExp_eq_linkChain P _ bs Is h.2]
    change linkChain P (LinkedG.compTripleS P ⟨e, b, w⟩ I) (I.store, e.init) bs Is = _
    rw [compTripleS_eq_linkS h.1]
    exact linkChain_mapStore P bs Is (Equiv.prodComm _ _) _ (e.init, I.store)

theorem linkChain_cons_eq (P : Profile) :
    ∀ (b : SimpleI) (w : List Nat) (I : ScalarInstance) (bs : List (SimpleI × List Nat))
      (Is : List ScalarInstance) {S : Type}
      (T : ObsTriple (sigN 0) S (Nat × Payload) (Payload ⊕ PUnit)) (s : S),
      linkChain P T s ((b, w) :: bs) (I :: Is) =
        threadS (linkS T (impStackT P b w I bs Is).2.1) (s, (impStackT P b w I bs Is).2.2)
  | _, _, _, [], [], _, _, _ => rfl
  | _, _, _, [], _ :: _, _, _, _ => rfl
  | _, _, _, (_, _) :: _, [], _, _, _ => rfl
  | b, w, I, (b', w') :: bs, I' :: Is, _, T, s => by
    change linkChain P (linkS T (b.impTripleS P w I)) (s, I.store) ((b', w') :: bs) (I' :: Is) =
      threadS (linkS T (linkS (b.impTripleS P w I) (impStackT P b' w' I' bs Is).2.1))
        (s, (I.store, (impStackT P b' w' I' bs Is).2.2))
    rw [linkChain_cons_eq P b' w' I' bs Is, linkS_assoc]
    exact Silmaril.Wasm.Component.Reference.threadS_mapStore (Equiv.prodAssoc _ _ _).symm _
      (s, (I.store, _))

/-! ## Compositions of sessions, `profile o` -/

variable {o : GrowOracle}

theorem retDet_impStackT :
    ∀ (b : SimpleI) (w : List Nat) (I : ScalarInstance) (bs : List (SimpleI × List Nat))
      (Is : List ScalarInstance), RetDet (impStackT (profile o) b w I bs Is).2.1
  | _, _, _, [], _ => SimpleI.retDet_impTripleS o
  | _, _, _, (_, _) :: _, [] => SimpleI.retDet_impTripleS o
  | _, _, _, (b', w') :: bs, I' :: Is =>
    retDet_linkS (SimpleI.retDet_impTripleS o) (retDet_impStackT b' w' I' bs Is)

theorem threadS_impStackT :
    ∀ (b : SimpleI) (w : List Nat) (I : ScalarInstance) (bs : List (SimpleI × List Nat))
      (Is : List ScalarInstance),
      threadS (impStackT (profile o) b w I bs Is).2.1 (impStackT (profile o) b w I bs Is).2.2 =
        impStack (profile o) b w I bs Is
  | _, _, _, [], _ => rfl
  | _, _, _, (_, _) :: _, [] => rfl
  | b, w, I, (b', w') :: bs, I' :: Is => by
    change threadS (linkS (b.impTripleS (profile o) w I) (impStackT (profile o) b' w' I' bs Is).2.1)
        (I.store, (impStackT (profile o) b' w' I' bs Is).2.2) =
      (b.impSession (profile o) w I).comp (impStack (profile o) b' w' I' bs Is)
    rw [← threadS_impStackT b' w' I' bs Is]
    exact (comp_threadS SimpleI.noPlainTrap_impTripleS
      (storeDet_of_retDet (SimpleI.retDet_impTripleS o))
      (storeDet_of_retDet (retDet_linkS (SimpleI.retDet_impTripleS o)
        (retDet_impStackT b' w' I' bs Is))) _ _).symm

/-- **One link is the composition of the two sessions** (`profile o`). -/
theorem session_toExp_eq_comp {e : ExpSpec} {b : SimpleI} {w : List Nat} {I : ScalarInstance}
    (hd : e.Det (profile o)) (hw : (LinkedG.mk e b w).WireTy) :
    (LinkedG.toExp ⟨e, b, w⟩ I).session (profile o) =
      (e.session (profile o)).comp (b.impSession (profile o) w I) := by
  change threadS (LinkedG.compTripleS (profile o) ⟨e, b, w⟩ I) (I.store, e.init) = _
  rw [compTripleS_eq_linkS hw]
  refine (Silmaril.Wasm.Component.Reference.threadS_mapStore (Equiv.prodComm _ _) _
    (e.init, I.store)).trans ?_
  exact (comp_threadS ExpSpec.noPlainTrap_sessTripleS (ExpSpec.storeDet_sessTripleS hd)
    (storeDet_of_retDet (retDet_linkS (retDet_sessTripleS hd) (SimpleI.retDet_impTripleS o)))
    _ _).symm

theorem session_chainExp_eq_sessChain :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance),
      e.Det (profile o) → ChainWire e bs Is →
      (chainExp e bs Is).session (profile o) = sessChain (profile o) (e.session (profile o)) bs Is
  | _, [], _, _, _ => rfl
  | _, (_, _) :: _, [], _, _ => rfl
  | e, (b, w) :: bs, I :: Is, hd, h => by
    change (chainExp (LinkedG.toExp ⟨e, b, w⟩ I) bs Is).session (profile o) =
      sessChain (profile o) ((e.session (profile o)).comp (b.impSession (profile o) w I)) bs Is
    rw [session_chainExp_eq_sessChain _ bs Is (LinkedG.toExp_det hd) h.2,
      session_toExp_eq_comp hd h.1]

theorem sessChain_cons_eq (P : Profile) :
    ∀ (b : SimpleI) (w : List Nat) (I : ScalarInstance) (bs : List (SimpleI × List Nat))
      (Is : List ScalarInstance) (S : DStrategy (sigN 0) sessSig),
      sessChain P S ((b, w) :: bs) (I :: Is) = S.comp (impStack P b w I bs Is)
  | _, _, _, [], [], _ => rfl
  | _, _, _, [], _ :: _, _ => rfl
  | _, _, _, (_, _) :: _, [], _ => rfl
  | b, w, I, (b', w') :: bs, I' :: Is, S => by
    change sessChain P (S.comp (b.impSession P w I)) ((b', w') :: bs) (I' :: Is) =
      S.comp ((b.impSession P w I).comp (impStack P b' w' I' bs Is))
    rw [sessChain_cons_eq P b' w' I' bs Is, DStrategy.comp_assoc]

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp
