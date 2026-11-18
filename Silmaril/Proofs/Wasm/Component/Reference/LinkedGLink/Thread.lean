module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Link
public import Silmaril.Wasm.Component.Reference.LinkedGSession.Thms
public import Silmaril.Games.Abstract.SessionLinkCoh.Thms
public import Silmaril.Games.Abstract.SessionLinkAssoc.Thms

/-!
# Sessions of transported and linked triples (proofs)

* `threadS_mapStore`: transporting a triple along a store equivalence does not change its
  session, from corresponding stores (`StratSession.threadS_eq_of_obsEq`, the graph of the
  equivalence being a bisimulation).
* `compSession_eq_threadS_linkS`: the session object of a linked component is the session of the
  linked triple.
* `compTripleS_toExp_eq_linkS`, `compSession_toExp_eq`: one more importer on a linked component,
  by `SessionLinkCoh.linkS_mapStore_left` and `SessionLinkAssoc.linkS_assoc`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore mapEnd linkS_assoc)
open Silmaril.Games.Abstract.SessionLinkCoh (sat_mapStore mapStore_trans linkS_mapStore_left)
open Silmaril.Games.Abstract.StratThread (IsBisim RoundEq)
open Silmaril.Games.Abstract.StratSession (threadS threadS_eq_of_obsEq)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

universe u

section Transport

variable {E : Sig.{u}} {S S' A B : Type u}

/-- The graph of a store equivalence is a bisimulation between a triple and its transport. -/
theorem isBisim_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    IsBisim (mapStore e t) t (fun x y => x = e y) := by
  rintro _ s rfl
  have hs : e.symm (e s) = s := e.symm_apply_apply s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c
    show (c, End.trap) ∈ (fun x => (x.1, mapEnd e x.2)) '' t.1 (e.symm (e s)) a ↔ _
    rw [hs]
    constructor
    · rintro ⟨⟨c', e'⟩, h, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, he⟩ := hx
      cases e' <;> simp [mapEnd] at he
      exact h
    · intro h
      exact ⟨_, h, rfl⟩
  · intro a c
    show (c, End.div) ∈ (fun x => (x.1, mapEnd e x.2)) '' t.1 (e.symm (e s)) a ↔ _
    rw [hs]
    constructor
    · rintro ⟨⟨c', e'⟩, h, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, he⟩ := hx
      cases e' <;> simp [mapEnd] at he
      exact h
    · intro h
      exact ⟨_, h, rfl⟩
  · have h : StratObs.satP (mapStore e t) (e s) = StratObs.satP t (e.symm (e s)) :=
      congrFun (congrArg (fun x => x.2.1) (sat_mapStore e t)) (e s)
    rw [h, hs]
  · show t.2.2 (e.symm (e s)) = t.2.2 s
    rw [hs]
  · rintro a c b s₁ ⟨⟨c', e'⟩, h, hx⟩
    rw [hs] at h
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, he⟩ := hx
    cases e' with
    | ret b' s₀ =>
      simp only [mapEnd, End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨s₀, h, rfl⟩
    | trap => simp [mapEnd] at he
    | div => simp [mapEnd] at he
  · intro a c b s₁ h
    refine ⟨e s₁, ⟨(c, End.ret b s₁), ?_, rfl⟩, rfl⟩
    show (c, End.ret b s₁) ∈ t.1 (e.symm (e s)) a
    rw [hs]
    exact h

/-- **Transport does not change the session**, from corresponding stores. -/
theorem threadS_mapStore (e : S ≃ S') (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S) :
    threadS (mapStore e t) (e s) = threadS t s :=
  threadS_eq_of_obsEq ⟨_, isBisim_mapStore e t, rfl⟩

end Transport

variable {P : Profile}

/-- **The session object of a linked component is the session of the linked triple.** -/
theorem compSession_eq_threadS_linkS {g : LinkedG} {Ii : ScalarInstance}
    (hI : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    LinkedG.compSession P g =
      threadS (linkS (g.exp.sessTripleS P) (g.imp.impTripleS P g.wire Ii)) (g.exp.init, Ii.store) := by
  rw [LinkedG.compSession_eq hI, compTripleS_eq_linkS hw]
  exact threadS_mapStore (Equiv.prodComm g.exp.St (Store Nat)) _ (g.exp.init, Ii.store)

/-- **One more importer on a linked component**: the triple of the chain is the base exporter
serving the two importers linked together, along a store equivalence. -/
theorem compTripleS_toExp_eq_linkS {g : LinkedG} {Ii : ScalarInstance} {b : SimpleI}
    {w : List Nat} {I : ScalarInstance} (hw : g.WireTy)
    (hw' : (LinkedG.mk (g.toExp Ii) b w).WireTy) :
    LinkedG.compTripleS P ⟨g.toExp Ii, b, w⟩ I =
      mapStore ((Equiv.prodAssoc g.exp.St (Store Nat) (Store Nat)).symm.trans
        ((Equiv.prodCongr (Equiv.prodComm g.exp.St (Store Nat)) (Equiv.refl (Store Nat))).trans
          (Equiv.prodComm (Store Nat × g.exp.St) (Store Nat))))
        (linkS (g.exp.sessTripleS P)
          (linkS (g.imp.impTripleS P g.wire Ii) (b.impTripleS P w I))) := by
  refine (compTripleS_eq_linkS (g := ⟨g.toExp Ii, b, w⟩) (Ii := I) hw').trans ?_
  change mapStore _ (linkS (LinkedG.compTripleS P g Ii) _) = _
  rw [compTripleS_eq_linkS hw, linkS_mapStore_left, linkS_assoc, ← mapStore_trans,
    ← mapStore_trans]

/-- **The session object of one more importer on a linked component** is the session of the
base exporter serving the two importers linked together. -/
theorem compSession_toExp_eq {g : LinkedG} {Ii : ScalarInstance} {b : SimpleI}
    {w : List Nat} {I : ScalarInstance} (hw : g.WireTy)
    (hw' : (LinkedG.mk (g.toExp Ii) b w).WireTy) (hI : b.mod.IsInst I) :
    LinkedG.compSession P ⟨g.toExp Ii, b, w⟩ =
      threadS (linkS (g.exp.sessTripleS P)
          (linkS (g.imp.impTripleS P g.wire Ii) (b.impTripleS P w I)))
        (g.exp.init, (Ii.store, I.store)) := by
  rw [LinkedG.compSession_eq (g := ⟨g.toExp Ii, b, w⟩) hI, compTripleS_toExp_eq_linkS hw hw']
  exact threadS_mapStore _ _ (g.exp.init, (Ii.store, I.store))

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink
