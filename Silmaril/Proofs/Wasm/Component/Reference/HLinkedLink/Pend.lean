module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Inf
public import Silmaril.Games.Abstract.SessionLink.Thms
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# The pending calls of the generic link, and the open triple (proofs)

* The server forces only its host calls: a call prefix of the server is the routed host call
  itself (`satP_serverO`).
* **Pending calls** (`pend_eq`): the call prefixes of the open triple are the pending calls of
  the generic link. The link is saturated (`SessionLink.saturated_linkS`) and has the finished
  behaviours and streams of the open triple (`fin_eq`, `inf_eq`), so its call prefixes are those
  of the open triple. Conversely a pending call of the link is a host call the client waits on;
  answering it by a refusal traps the core instance at once (`path_refuse`), a finished behaviour
  of the open triple with that call as its last call.
* `compTripleOR_eq`: the open triple before restriction is the generic link, the stores
  reordered.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratObs (satP saturated_iff)
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.SessionRoute (callS mapS)
open Silmaril.Games.Abstract.StratSession (pairS)
open Silmaril.Games.Abstract.SessionExt (routeS foldS)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance Answer)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession (WTH wth_of)
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
  (hostCalls_append hostCalls_one_wired hostCalls_one_host)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "IRel" => Silmaril.Wasm.Component.Reference.ImpRel

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

/-- **The server forces only its host calls.** -/
theorem satP_serverO {σ : PUnit.{1} × Store Nat} {a : Nat × Payload}
    {x : List (Call (sigN l.host.length)) × (sigN l.host.length).Op}
    (h : x ∈ satP (l.serverO P Ie) σ a) : x.1 = [] ∧ l.route a = .inl x.2 := by
  obtain ⟨c, m'⟩ := x
  have hpend : (l.serverO P Ie).2.1 σ a =
      Sum.elim (fun m => {(([] : List (Call (sigN l.host.length))), m)}) (fun _ => ∅)
        (l.route a) := by
    show Sum.elim (l.hostPass.2.1 σ.1) ((l.expTripleH P Ie).2.1 σ.2) (l.route a) = _
    rcases l.route a with m | a' <;> rfl
  rcases hp : l.route a with m | a' <;> rw [hp] at hpend
  · rcases h with h | ⟨d, m'', hd, n, c', hc⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨ω, hω, -⟩
    · rw [hpend] at h
      simp only [Sum.elim_inl, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · rw [hpend] at hd
      simp only [Sum.elim_inl, Set.mem_singleton_iff, Prod.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      simp at hc
    · obtain ⟨n', hn'⟩ := (mem_serverO_inl hp).1 hd
      simp only [Prod.mk.injEq] at hn'
      obtain ⟨rfl, -⟩ := hn'
      cases c with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hc
        obtain ⟨hc, -⟩ := hc
        simp only [Sigma.mk.injEq] at hc
        exact ⟨rfl, by rw [hc.1]⟩
      | cons z c => simp at hc
    · rw [serverO_inf] at hω
      exact hω.elim
  · rcases h with h | ⟨d, m'', hd, -⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨ω, hω, -⟩
    · rw [hpend] at h; exact h.elim
    · rw [hpend] at hd; exact hd.elim
    · have := ((mem_serverO_inr hp).1 hd).1
      simp only at this
      subst this
      simp at hc
    · rw [serverO_inf] at hω
      exact hω.elim

theorem satP_linkO (σ : (PUnit.{1} × Store Nat) × Store Nat) (q : Nat × Payload) :
    satP (l.linkO P Ie Ii) σ q = (l.linkO P Ie Ii).2.1 σ q :=
  congrFun (congrFun (saturated_iff.1 SessionLink.saturated_linkS) σ) q

/-- **A pending call of the generic link, refused, is a finished behaviour of the open
triple**: the importer's core instance traps at once. -/
theorem refuse_mem (hw : l.WireTy) {u π : Store Nat} {q : Nat × Payload}
    {x : List (Call (sigN l.host.length)) × (sigN l.host.length).Op}
    (hx : x ∈ (l.linkO P Ie Ii).2.1 ((PUnit.unit, π), u) q) :
    ∃ σ : Store Nat × Store Nat, (x.1 ++ [⟨x.2, none⟩], End.ret (Sum.inr PUnit.unit) σ) ∈
      HLinked2.compFinO P l Ie Ii (u, π) q := by
    obtain ⟨rs, s₁, a, c, hR, hsatc, hsats, hx1⟩ := hx
    obtain ⟨j, vs, f, cs, dss, s, t, e, s', t', nm, ft, ws, rfl, hlow, hp, hpe, himp, hlift, hxa⟩ :=
      LinkedGLink.satP_impTripleS_subset (b := l.imp) (wire := l.wireH) _ _ hsatc
    simp only [Prod.mk.injEq] at hxa
    obtain ⟨hlog, rfl⟩ := hxa
    obtain ⟨hc0, hroute⟩ := satP_serverO hsats
    simp only at hc0
    subst hc0
    have hck : ValTy.checkList l.imp.exports[j].ty.params vs = true := by
      obtain ⟨j₀, vs₀, hjq, hck⟩ := LinkedGLink.typedQ_of_lowered hlow
      simp only [Prod.mk.injEq, Payload.vals.injEq] at hjq
      obtain ⟨hj, rfl⟩ := hjq
      obtain rfl : j₀ = j := Fin.ext hj.symm
      exact hck
    have hq : l.toL2.typedQ (j.val, .vals vs) = some (j, vs) :=
      LinkedSessionEquiv.typedQ_typed (l := l.toL2) hck
    have hk : e.1.val < l.imp.imports.length := LinkedGLink.lt_of_getElem? himp
    -- the pending call is a host call
    have hlen := imports_length hw
    by_cases hlt : e.1.val < l.wire.length
    · have hwk : l.wire[e.1.val]? = some l.wire[e.1.val] := List.getElem?_eq_getElem hlt
      obtain ⟨x', hx', -⟩ := hw.ty _ _ hwk
      have hwN : l.wire[e.1.val] < l.exp.exports.length := LinkedGLink.lt_of_getElem? hx'
      rw [wireH_getD_wired hwk, route_wired hwN] at hroute
      cases hroute
    let i : Fin l.host.length := ⟨e.1.val - l.wire.length, by omega⟩
    have hi : e.1.val = l.wire.length + i.val := by simp [i]; omega
    rw [hi, wireH_getD_host i, route_host i] at hroute
    obtain ⟨⟨⟩, π₁⟩ := s₁
    obtain ⟨hrun, hslog⟩ := expRunH_of_rounds hR dss.flatten
      (wth_flatten hw (LinkedGLink.lowered_forall₂ hlow)) hlog
    obtain ⟨hk', hrel⟩ := impRel_refuse (Ii := Ii) himp hlift
    -- the refused host call, then the trap
    set z : l.imp.ICall := ⟨(⟨e.1.val, hk'⟩, .vals ws), none⟩ with hz
    have hzh : l.hostCalls [z] = [⟨(i, .vals ws), none⟩] :=
      hostCalls_one_host (k := ⟨e.1.val, hk'⟩) i hi
    have hrun' : HLinked2.ExpRunH P l Ie π (dss ++ [[z]]).flatten π₁ := by
      rw [List.flatten_append, List.flatten_singleton]
      exact HLinkedSession.expRunH_append hrun (.host i hi (.nil _))
    let d : Linked2.SessRound l.toL2 Ii :=
      ⟨j, vs, f, cs ++ [(⟨e, Answer.trap⟩ : Σ e : Ii.E.Op, Ii.E.Ar e)], Answer.trap, dss ++ [[z]]⟩
    have hok : d.Ok := LinkedGLink.lowered_append hlow (.cons hrel .nil)
    have hcm : (callMoves (cs ++ [(⟨e, Answer.trap⟩ : Σ e : Ii.E.Op, Ii.E.Ar e)]) :
        List (Move Ii.E Ii.F)) = callMoves cs ++ [.inl (.ask e), .inl (.ans e Answer.trap)] := by
      rw [LinkedGLink.callMoves_append]
      rfl
    have hpath : Ii.Path P (.idle u) d.instMoves (.idle s') := by
      have := LinkedGLink.path_append hp (path_refuse hpe)
      show Ii.Path P (.idle u) (.inr (.ask f) :: callMoves (cs ++ [⟨e, Answer.trap⟩]) ++
        [.inr (.ans f Answer.trap)]) (.idle s')
      rw [hcm]
      simpa using this
    have hspec : HLinked2.SessSpec P l Ie Ii u π [(j, vs)] [none]
        [l.hostCalls (dss ++ [[z]]).flatten] s' π₁ :=
      .round d hok hpath hrun' rfl (.nil _ _)
    have hmem : (l.hostCalls (dss ++ [[z]]).flatten, End.ret (outAns none) (s', π₁)) ∈
        HLinked2.compFinO P l Ie Ii (u, π) (j.val, .vals vs) := by
      simp only [HLinked2.compFinO, hq]
      exact .inl ⟨none, s', π₁, hspec, rfl⟩
    have hlog' : l.hostCalls (dss ++ [[z]]).flatten = x.1 ++ [⟨x.2, none⟩] := by
      rw [List.flatten_append, List.flatten_singleton, hostCalls_append, hzh, ← hslog, hx1]
      simp only [List.append_nil, Sum.inl.injEq] at hroute ⊢
      rw [← hroute]
    refine ⟨(s', π₁), ?_⟩
    rw [← hlog']
    exact hmem

/-- **The pending calls of the generic link are the call prefixes of the open triple.** -/
theorem pend_eq (hw : l.WireTy) (u π : Store Nat) (q : Nat × Payload) :
    satP (HLinked2.compFinO P l Ie Ii, fun _ _ => ∅, HLinked2.compInfO P l Ie Ii) (u, π) q =
      (l.linkO P Ie Ii).2.1 ((PUnit.unit, π), u) q := by
  ext x
  constructor
  · rintro (h | ⟨d, m', h, -⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, hk, hm⟩)
    · exact h.elim
    · exact h.elim
    · have hd' : (d, e) ∈ HLinked2.compFinO P l Ie Ii (u, π) q := hd
      rw [fin_eq hw] at hd'
      obtain ⟨x', hx', hxe⟩ := hd'
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, -⟩ := hxe
      rw [← satP_linkO]
      exact .inr (.inr (.inl ⟨x'.1, x'.2, hx', hc⟩))
    · have hω' : ω ∈ HLinked2.compInfO P l Ie Ii (u, π) q := hω
      rw [inf_eq hw] at hω'
      rw [← satP_linkO]
      exact .inr (.inr (.inr ⟨ω, hω', k, hk, hm⟩))
  · intro hx
    obtain ⟨σ, hσ⟩ := refuse_mem hw hx
    exact .inr (.inr (.inl ⟨_, _, hσ, none, [], rfl⟩))

/-- **The open triple before restriction is the generic link**, the stores reordered. -/
theorem compTripleOR_eq (hw : l.WireTy) :
    HLinked2.compTripleOR P l Ie Ii =
      SessionLinkAssoc.mapStore HLinked2.storeEquiv (l.linkO P Ie Ii) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext σ q
    obtain ⟨u, π⟩ := σ
    exact fin_eq hw u π q
  · funext σ q
    obtain ⟨u, π⟩ := σ
    exact pend_eq hw u π q
  · funext σ q
    obtain ⟨u, π⟩ := σ
    exact inf_eq hw u π q

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
