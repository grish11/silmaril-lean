module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Pend
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.RetT
public import Silmaril.Games.Abstract.StratLegal.Defs
public import Silmaril.Games.Abstract.SessionExt.Thms
public import Silmaril.Games.Abstract.SessionRoute.Thms
public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGDet.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGLink.Thms
import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR

/-!
# The open and the host-realizable objects through the generic link (proofs)

* `restrict_mapStore`: the legal restriction commutes with transport along a store
  equivalence (a generic fact about `StratLegal.restrict` and `SessionLinkAssoc.mapStore`, proved
  here).
* `compTripleO_eq_linkS`, `compSessionO_eq_threadS`: the open triple is the legal restriction of
  the generic link; the open session object is its session.
* `compTripleR_eq_realize`: the host-realizable triple is the realizable restriction
  (`HLinked2.realize`) of the open triple before restriction, hence of the generic link
  (`compTripleR_eq_realize_linkS`, `compSession_eq_threadS_realize`).
* `comp_threadS_linkO`, `threadS_serverO`: at `profile o` the session of the generic link is the
  server's session composed with the client's, and the server's session is the host passthrough
  handler beside the exporter's session below the routing handler.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore)
open Silmaril.Games.Abstract.StratSession (threadS NoPlainTrap)
open Silmaril.Games.Abstract.SessionCat (RetDet)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-! ## Restriction and transport -/

/-- **The legal restriction commutes with transport along a store equivalence.** -/
theorem restrict_mapStore {E : Sig.{0}} {S S' A B : Type} {L : (m : E.Op) → E.Ar m → Prop}
    (e : S ≃ S') (t : ObsTriple E S A B) :
    StratLegal.restrict L (mapStore e t) = mapStore e (StratLegal.restrict L t) := by
  refine Prod.ext ?_ rfl
  funext s a
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(x.1, y.2), ?_, ?_⟩
    · have h1 : y.1 = x.1.map StratLegal.liftCall := congrArg Prod.fst hyx
      show (x.1.map StratLegal.liftCall, y.2) ∈ t.1 (e.symm s) a
      rw [← h1]
      exact hy
    · have h2 : SessionLinkAssoc.mapEnd e y.2 = x.2 := congrArg Prod.snd hyx
      show (x.1, SessionLinkAssoc.mapEnd e y.2) = x
      rw [h2]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y.1.map StratLegal.liftCall, y.2), hy, rfl⟩

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

/-! ## The open object -/

theorem compTripleO_eq_restrict :
    HLinked2.compTripleO P l Ie Ii =
      StratLegal.restrict (HLinked2.hostLegal l.host) (HLinked2.compTripleOR P l Ie Ii) := rfl

/-- **The open triple is the legal restriction of the generic link**, the stores reordered. -/
theorem compTripleO_eq_linkS (hw : l.WireTy) :
    HLinked2.compTripleO P l Ie Ii =
      mapStore HLinked2.storeEquiv
        (StratLegal.restrict (HLinked2.hostLegal l.host) (l.linkO P Ie Ii)) := by
  rw [← restrict_mapStore, ← compTripleOR_eq hw]
  rfl

/-- **The open session object is the session of the restricted generic link.** -/
theorem compSessionO_eq_threadS (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    HLinked2.compSessionO P l =
      threadS (StratLegal.restrict (HLinked2.hostLegal l.host) (l.linkO P Ie Ii))
        ((PUnit.unit, Ie.store), Ii.store) := by
  have h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii :=
    ⟨Ie, Ii, hIe, hIi⟩
  rw [HLinked2.compSessionO, dite_eq_left_of_eq_true (eq_true h)]
  obtain rfl := NumModule.IsInst.unique h.choose_spec.choose_spec.1 hIe
  obtain rfl := ImpModule.IsInst.unique h.choose_spec.choose_spec.2 hIi
  rw [compTripleO_eq_linkS hw]
  exact threadS_mapStore HLinked2.storeEquiv _ ((PUnit.unit, h.choose.store), _)

/-! ## The host-realizable object -/

/-- **The host-realizable triple is the realizable restriction of the open triple.** -/
theorem compTripleR_eq_realize :
    HLinked2.compTripleR P l Ie Ii = HLinked2.realize l.host (HLinked2.compTripleOR P l Ie Ii) := by
  unfold HLinked2.compTripleR HLinked2.realize
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · funext s q
    obtain ⟨u, π, R⟩ := s
    ext ⟨c, e⟩
    show (c, e) ∈ HLinked2.compFin P l Ie Ii (u, π, R) q ↔
      ((∃ R' e', (c, e') ∈ HLinked2.compFinO P l Ie Ii (u, π) q ∧ HLinked2.VisRun l.host R c R' ∧
          e = HLinked2.attachR R' e') ∨
        (∃ m R' σ, (c ++ [⟨m, none⟩], End.ret (.inr PUnit.unit) σ) ∈
          HLinked2.compFinO P l Ie Ii (u, π) q ∧ HLinked2.VisRun l.host R c R' ∧
          HLinked2.Forced l.host R' m ∧ e = .ret (.inr PUnit.unit) (σ.1, σ.2, R')))
    unfold HLinked2.compFin HLinked2.compFinO
    rcases hq : l.toL2.typedQ q with _ | ⟨j, vs⟩
    · simp only
      constructor
      · intro h
        rw [Set.mem_singleton_iff] at h
        cases h
        exact .inl ⟨R, .ret (.inr PUnit.unit) (u, π), rfl, .nil R, rfl⟩
      · rintro (⟨R', e', he', hv, rfl⟩ | ⟨m, R', σ, hm, -, -, -⟩)
        · rw [Set.mem_singleton_iff] at he'
          simp only [Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          cases hv
          rfl
        · rw [Set.mem_singleton_iff] at hm
          simp at hm
    · simp only
      constructor
      · rintro (⟨o, u', π', R', hs, hv, rfl⟩ | ⟨m, u', π', R', hs, hv, hf, rfl⟩ |
          ⟨R', hd, hv, rfl⟩)
        · exact .inl ⟨R', .ret (outAns o) (u', π'), .inl ⟨o, u', π', hs, rfl⟩, hv, rfl⟩
        · exact .inr ⟨m, R', (u', π'), .inl ⟨none, u', π', hs, rfl⟩, hv, hf, rfl⟩
        · exact .inl ⟨R', .div, .inr ⟨hd, rfl⟩, hv, rfl⟩
      · rintro (⟨R', e', he', hv, rfl⟩ | ⟨m, R', σ, hm, hv, hf, rfl⟩)
        · rcases he' with ⟨o, u', π', hs, rfl⟩ | ⟨hd, rfl⟩
          · exact .inl ⟨o, u', π', R', hs, hv, rfl⟩
          · exact .inr (.inr ⟨R', hd, hv, rfl⟩)
        · rcases hm with ⟨o, u', π', hs, he⟩ | ⟨-, he⟩
          · simp only [End.ret.injEq] at he
            obtain ⟨ho, rfl⟩ := he
            obtain rfl : o = none := by cases o <;> simp_all [outAns]
            exact .inr (.inl ⟨m, u', π', R', hs, hv, hf, rfl⟩)
          · cases he
  · funext s q
    obtain ⟨u, π, R⟩ := s
    ext ω
    show ω ∈ HLinked2.compInf P l Ie Ii (u, π, R) q ↔
      ω ∈ HLinked2.compInfO P l Ie Ii (u, π) q ∧
        ∀ n, ∃ R', HLinked2.VisRun l.host R (streamTake ω n) R'
    unfold HLinked2.compInf HLinked2.compInfO
    rcases hq : l.toL2.typedQ q with _ | ⟨j, vs⟩
    · simp
    · exact Iff.rfl

/-- **The host-realizable triple is the realizable restriction of the generic link.** -/
theorem compTripleR_eq_realize_linkS (hw : l.WireTy) :
    HLinked2.compTripleR P l Ie Ii =
      HLinked2.realize l.host (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii)) := by
  rw [compTripleR_eq_realize, compTripleOR_eq hw]

/-- **The canonical session object is the session of the realizable restriction of the generic
link.** -/
theorem compSession_eq_threadS_realize (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    HLinked2.compSession P l =
      threadS (StratLegal.restrict (HLinked2.hostLegal l.host)
          (HLinked2.realize l.host (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))))
        (Ii.store, Ie.store, []) := by
  have h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii :=
    ⟨Ie, Ii, hIe, hIi⟩
  rw [HLinked2.compSession, dite_eq_left_of_eq_true (eq_true h)]
  obtain rfl := NumModule.IsInst.unique h.choose_spec.choose_spec.1 hIe
  obtain rfl := ImpModule.IsInst.unique h.choose_spec.choose_spec.2 hIi
  rw [HLinked2.compTripleS, compTripleR_eq_realize_linkS hw]

/-! ## What the realizable restriction removes -/

/-- The host calls of a finished behaviour of the host-realizable triple are a `VisRun`. -/
theorem visRun_of_mem_compFin {s : l.St} {q : Nat × Payload}
    {x : List (Call (sigN l.host.length)) × End l.St (Payload ⊕ PUnit.{1})}
    (h : x ∈ HLinked2.compFin P l Ie Ii s q) : ∃ R', HLinked2.VisRun l.host s.2.2 x.1 R' := by
  unfold HLinked2.compFin at h
  split at h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨_, .nil _⟩
  · rcases h with ⟨_, _, _, R', _, hv, _⟩ | ⟨_, _, _, R', _, hv, _, _⟩ | ⟨R', _, hv, _⟩ <;>
      exact ⟨R', hv⟩

/-- **A forced refusal is never visible**: no `VisRun` continues with a call forced at its
end. -/
theorem not_visRun_forced {h : Iface} {R R' R'' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} {m : (sigN h.length).Op} {n : Option Payload}
    (hc : HLinked2.VisRun h R c R') (hf : HLinked2.Forced h R' m) :
    ¬ HLinked2.VisRun h R (c ++ [⟨m, n⟩]) R'' := by
  intro hv
  obtain ⟨R₁, h₁, h₂⟩ := HLinkedSessionObj.visRun_split hv
  obtain rfl := HLinkedSessionObj.visRun_det hc h₁
  cases h₂ with
  | refuse hF _ => exact hF hf
  | @answer _ _ _ p _ hm hl _ =>
    rcases hf with hf | hf
    · exact hm hf
    · rcases p with ys | us
      · exact hl
      · exact hf ⟨us, hl⟩

/-- **The host-realizable triple shows no forced refusal**: a finished behaviour whose host calls
are `c` followed by a call `m` has `m` unforced at the end of `c`. -/
theorem forced_not_visible {u π : Store Nat} {R R' : List (sigN l.host.length).Op}
    {q : Nat × Payload} {c : List (Call (sigN l.host.length))} {m : (sigN l.host.length).Op}
    {n : Option Payload} {e : End l.St (Payload ⊕ PUnit.{1})}
    (hx : (c ++ [⟨m, n⟩], e) ∈ (HLinked2.compTripleR P l Ie Ii).1 (u, π, R) q)
    (hc : HLinked2.VisRun l.host R c R') : ¬ HLinked2.Forced l.host R' m := by
  intro hf
  obtain ⟨R'', hv⟩ := visRun_of_mem_compFin hx
  exact not_visRun_forced hc hf hv

/-! ## Composition of sessions -/

theorem noPlainTrap_expTripleH : NoPlainTrap (l.expTripleH P Ie) := by
  rintro s a c ⟨-, -, h⟩
  rcases h with ⟨-, h⟩ | ⟨-, ⟨R, s', hst, h⟩ | ⟨-, h⟩⟩ <;> cases h

theorem retDet_expTripleH (o : GrowOracle) : RetDet (l.expTripleH (profile o) Ie) := by
  rintro s a c c' b b' s₁ s₁' ⟨rfl, h1⟩ ⟨rfl, h2⟩
  exact Simple.afunDet_sessTripleS o l.exp Ie s a _ _ h1 h2

theorem noPlainTrap_serverO : NoPlainTrap (l.serverO P Ie) :=
  SessionExt.noPlainTrap_routeS l.route SessionRoute.noPlainTrap_callS noPlainTrap_expTripleH

theorem retDet_serverO (o : GrowOracle) : RetDet (l.serverO (profile o) Ie) :=
  SessionExt.retDet_routeS l.route SessionRoute.retDet_callS (retDet_expTripleH o)

/-- **The server's session is the host passthrough beside the exporter's session**, below the
routing handler (`profile o`). -/
theorem threadS_serverO (o : GrowOracle) (π : Store Nat) :
    threadS (l.serverO (profile o) Ie) (PUnit.unit, π) =
      ((DStrategy.ofHandler (SessionRoute.callH (E := sigN l.host.length) id
          fun _ n => ExpSpec.sumAns n)).pair (threadS (l.expTripleH (profile o) Ie) π)).comp
        (DStrategy.ofHandler (SessionExt.routeH l.route)) := by
  rw [← SessionRoute.threadS_callS]
  exact (SessionExt.pair_comp_routeH l.route SessionRoute.noPlainTrap_callS
    SessionRoute.retDet_callS noPlainTrap_expTripleH (retDet_expTripleH o) PUnit.unit π).symm

/-- **The generic link is the composition of the server's and the client's sessions**
(`profile o`). -/
theorem comp_threadS_linkO (o : GrowOracle) (π u : Store Nat) :
    (threadS (l.serverO (profile o) Ie) (PUnit.unit, π)).comp
        (threadS (l.clientH (profile o) Ii) u) =
      threadS (l.linkO (profile o) Ie Ii) ((PUnit.unit, π), u) :=
  SessionLink.comp_threadS noPlainTrap_serverO
    (SessionCat.storeDet_of_retDet (retDet_serverO o))
    (SessionCat.storeDet_of_retDet
      (SessionCat.retDet_linkS (retDet_serverO o) (SimpleI.retDet_impTripleS o))) _ _

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
