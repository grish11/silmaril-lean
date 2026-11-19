module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.RealServer
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Main

/-!
# The host-realizable object is a generic link (proofs)

`compTripleR_eq_linkR`: the host-realizable triple of `HLinked2` is exactly the generic link of
the host-realizable server (`HLinked2.serverR`: the realizability host `hostTripleR` beside the
exporter) serving the importer's own triple, the stores reordered by `storeEquivR`.

The proof compares the host-realizable link with the passthrough link, whose realizable
restriction is the host-realizable triple (`compTripleR_eq_realize_linkS`):

* a returning round of the realizable link is a passthrough round whose host calls are a
  `VisRun` from `R`, or one whose last served call is a forced refusal hidden by `serverR`; a trap
  answer ends the client's round (`SimpleI.impTripleS_trapAbortsRound`), so a hidden refusal is the
  last call and the round returns the trap;
* divergences and streams receive no trap answer, so they are visible;
* a pending call of the realizable link is an unforced host call; refused, it is a visible
  refusal followed by the trap of the importer's core instance (`refuse_mem`), a finished
  behaviour of the realizable restriction.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratObs (satP CallPre saturated_iff)
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.StratSession (threadS NoPlainTrap)
open Silmaril.Games.Abstract.SessionCat (RetDet)
open Silmaril.Games.Abstract.SessionTrap (TrapEnd)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component.Reference.HLinked2 (VisRun Forced hostLegal hostTripleR)

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

/-! ## Traps of the client -/

theorem trapLast_fin {u : Store Nat} {q : Nat × Payload} {L : List (Call sigS)}
    {e : End (Store Nat) (Payload ⊕ PUnit.{1})} (h : (L, e) ∈ (l.clientH P Ii).1 u q) :
    TrapLast L := fun L₁ z L₂ hL hz =>
  ((LinkedGLink.impTripleS_trapAbortsRound (b := l.imp) (wire := l.wireH) (P := P)
    (I := Ii)).beh u q L₁ z.1 z.2 L₂ e hz (hL ▸ h)).1

theorem trap_end {u : Store Nat} {q : Nat × Payload} {L₁ : List (Call sigS)} {a : Nat × Payload}
    {e : End (Store Nat) (Payload ⊕ PUnit.{1})}
    (h : (L₁ ++ [⟨a, .inr PUnit.unit⟩], e) ∈ (l.clientH P Ii).1 u q) :
    ∃ u', e = .ret (.inr PUnit.unit) u' := by
  have hte := ((LinkedGLink.impTripleS_trapAbortsRound (b := l.imp) (wire := l.wireH) (P := P)
    (I := Ii)).beh u q L₁ a (.inr PUnit.unit) [] e rfl h).2
  rcases e with ⟨x, u'⟩ | _ | _
  · rcases x with x | ⟨⟩
    · exact hte.elim
    · exact ⟨u', rfl⟩
  · exact (LinkedGLink.noPlainTrap_impTripleS (b := l.imp) (wire := l.wireH) (P := P) (I := Ii)
      u q _ h).elim
  · exact hte.elim

theorem noTrap_satP {u : Store Nat} {q : Nat × Payload} {L : List (Call sigS)} {a : Nat × Payload}
    (h : (L, a) ∈ satP (l.clientH P Ii) u q) :
    ∀ L₁ z L₂, L = L₁ ++ z :: L₂ → z.2 ≠ .inr PUnit.unit := by
  intro L₁ z L₂ hL hz
  have hp := LinkedGLink.satP_impTripleS_subset (b := l.imp) (wire := l.wireH) (P := P) (I := Ii)
    u q h
  rw [hL] at hp
  exact (LinkedGLink.impTripleS_trapAbortsRound (b := l.imp) (wire := l.wireH) (P := P)
    (I := Ii)).pend u q L₁ z.1 z.2 L₂ a hz hp

theorem noTrap_inf {u : Store Nat} {q : Nat × Payload} {ω : ℕ → Call sigS}
    (h : ω ∈ (l.clientH P Ii).2.2 u q) : ∀ k, (ω k).2 ≠ .inr PUnit.unit := fun k hk =>
  (LinkedGLink.impTripleS_trapAbortsRound (b := l.imp) (wire := l.wireH) (P := P)
    (I := Ii)).inf u q ω h k hk

/-! ## Bookkeeping -/

theorem attachR_linkEnd (R' : List (sigN l.host.length).Op) (π₁ : Store Nat)
    (eC : End (Store Nat) (Payload ⊕ PUnit.{1})) :
    HLinked2.attachR R' (SessionLinkAssoc.mapEnd HLinked2.storeEquiv
      (linkEnd (PUnit.unit, π₁) eC)) =
      SessionLinkAssoc.mapEnd (HLinked2.storeEquivR l.host) (linkEnd (R', π₁) eC) := by
  rcases eC with ⟨x, u'⟩ | _ | _ <;> rfl

theorem logTake_prefix {E : Sig.{0}} (lg : ℕ → List (Call E)) {k n : ℕ} (h : k ≤ n) :
    ∃ d, logTake lg n = logTake lg k ++ d := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            exact ⟨[], rfl⟩
  | succ n ih =>
    by_cases hk : k = n + 1
    · subst hk; exact ⟨[], (List.append_nil _).symm⟩
    · obtain ⟨d, hd⟩ := ih (by omega)
      exact ⟨d ++ lg n, by rw [logTake_succ, hd, List.append_assoc]⟩

theorem div_log_nil {σ : PUnit.{1} × Store Nat} {a : Nat × Payload}
    {c : List (Call (sigN l.host.length))} (h : (c, End.div) ∈ (l.serverO P Ie).1 σ a) : c = [] := by
  obtain ⟨⟨⟩, π⟩ := σ
  rcases hr : l.route a with m | a'
  · obtain ⟨n, hn⟩ := (mem_serverO_inl hr).1 h
    simp at hn
  · exact ((mem_serverO_inr hr).1 h).1

theorem satP_linkR (σ : (List (sigN l.host.length).Op × Store Nat) × Store Nat)
    (q : Nat × Payload) : satP (l.linkR P Ie Ii) σ q = (l.linkR P Ie Ii).2.1 σ q :=
  congrFun (congrFun (saturated_iff.1 SessionLink.saturated_linkS) σ) q

/-! ## Finished behaviours -/

theorem finR_eq (u π : Store Nat) (R : List (sigN l.host.length).Op) (q : Nat × Payload) :
    (HLinked2.realize l.host (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))).1 (u, π, R) q =
      (fun x => (x.1, SessionLinkAssoc.mapEnd (HLinked2.storeEquivR l.host) x.2)) ''
        (l.linkR P Ie Ii).1 ((R, π), u) q := by
  ext ⟨c, e⟩
  constructor
  · rintro (⟨R', e', ⟨⟨yc, ye⟩, hy, hye⟩, hv, rfl⟩ | ⟨m, R', σ, ⟨⟨yc, ye⟩, hy, hye⟩, hv, hf, rfl⟩)
    · simp only [Prod.mk.injEq] at hye
      obtain ⟨rfl, rfl⟩ := hye
      rcases hy with ⟨rs, s₁, eC, hR, hc, hyeq⟩ | ⟨rs, s₁, a, c', hR, hsat, hsrv, hyeq⟩ |
        ⟨ω, hω, lg, st, n, hinf, hn, hyeq⟩
      · simp only [Prod.mk.injEq] at hyeq
        obtain ⟨rfl, rfl⟩ := hyeq
        obtain ⟨⟨⟩, π₁⟩ := s₁
        obtain ⟨rsR, hRR, hsv, hlog⟩ := rounds_OR hR hv
        refine ⟨(servedLog rsR, linkEnd (R', π₁) eC), .inl ⟨rsR, _, eC, hRR, ?_, rfl⟩, ?_⟩
        · rw [hsv]; exact hc
        · rw [hlog, attachR_linkEnd]
      · simp only [Prod.mk.injEq] at hyeq
        obtain ⟨rfl, rfl⟩ := hyeq
        obtain ⟨⟨⟩, π₁⟩ := s₁
        obtain ⟨R₁, hv₁, -⟩ := HLinkedSessionObj.visRun_split hv
        obtain ⟨rsR, hRR, hsv, hlog⟩ := rounds_OR hR hv₁
        refine ⟨(servedLog rsR ++ c', .div), .inr (.inl ⟨rsR, (R₁, π₁), a, c', hRR, ?_,
          div_RO.2 hsrv, rfl⟩), ?_⟩
        · rw [hsv]; exact hsat
        · rw [hlog]; rfl
      · simp only [Prod.mk.injEq] at hyeq
        obtain ⟨rfl, rfl⟩ := hyeq
        have hall : ∀ k, ∃ R'', VisRun l.host R (logTake lg k) R'' := by
          intro k
          by_cases hk : k ≤ n
          · obtain ⟨d, hd⟩ := logTake_prefix lg hk
            rw [hd] at hv
            obtain ⟨R₁, hv₁, -⟩ := HLinkedSessionObj.visRun_split hv
            exact ⟨R₁, hv₁⟩
          · have := logTake_stable (lg := lg) (n := n) hn (k - n)
            rw [show n + (k - n) = k by omega] at this
            rw [this]
            exact ⟨R', hv⟩
        obtain ⟨stR, hinfR, -⟩ := inf_OR hinf hall
        exact ⟨(logTake lg n, .div), .inr (.inr ⟨ω, hω, lg, stR, n, hinfR, hn, rfl⟩), rfl⟩
    · simp only [Prod.mk.injEq] at hye
      obtain ⟨rfl, hye⟩ := hye
      rcases hy with ⟨rs, s₁, eC, hR, hc, hyeq⟩ | ⟨rs, s₁, a, c', hR, hsat, hsrv, hyeq⟩ |
        ⟨ω, hω, lg, st, n, hinf, hn, hyeq⟩
      · simp only [Prod.mk.injEq] at hyeq
        obtain ⟨hlogO, rfl⟩ := hyeq
        obtain ⟨⟨⟩, π₁⟩ := s₁
        rcases eC with ⟨x, u'⟩ | _ | _
        rotate_left
        · simp [linkEnd, SessionLinkAssoc.mapEnd] at hye
        · simp [linkEnd, SessionLinkAssoc.mapEnd] at hye
        simp only [linkEnd, SessionLinkAssoc.mapEnd, End.ret.injEq] at hye
        obtain ⟨rfl, rfl⟩ := hye
        obtain ⟨rsR, hRR, hsv, hlog⟩ := rounds_OR_hidden hR hlogO.symm hv hf (trapLast_fin hc)
        refine ⟨(servedLog rsR, linkEnd (R', π₁) (.ret (.inr PUnit.unit) u')),
          .inl ⟨rsR, _, _, hRR, ?_, rfl⟩, ?_⟩
        · rw [hsv]; exact hc
        · rw [hlog]; rfl
      · simp only [Prod.mk.injEq] at hyeq
        rw [hyeq.2] at hye
        cases hye
      · simp only [Prod.mk.injEq] at hyeq
        rw [hyeq.2] at hye
        cases hye
  · rintro ⟨⟨yc, ye⟩, hy, hye⟩
    simp only [Prod.mk.injEq] at hye
    obtain ⟨rfl, rfl⟩ := hye
    rcases hy with ⟨rs, s₁, eC, hR, hc, hyeq⟩ | ⟨rs, s₁, a, c', hR, hsat, hsrv, hyeq⟩ |
      ⟨ω, hω, lg, st, n, hinf, hn, hyeq⟩
    · simp only [Prod.mk.injEq] at hyeq
      obtain ⟨rfl, rfl⟩ := hyeq
      obtain ⟨R₁, π₁⟩ := s₁
      obtain ⟨rsO, hRO, hsv, hcase⟩ := rounds_RO hR (trapLast_fin hc)
      have hcO : (served rsO, eC) ∈ (l.clientH P Ii).1 u q := by rw [hsv]; exact hc
      rcases hcase with ⟨hlog, hv⟩ | ⟨m, hlog, hv, hf, L₁, a, hL⟩
      · refine .inl ⟨R₁, _, ⟨(servedLog rsO, linkEnd (PUnit.unit, π₁) eC),
          .inl ⟨rsO, _, eC, hRO, hcO, rfl⟩, by rw [hlog]⟩, hv, ?_⟩
        exact (attachR_linkEnd R₁ π₁ eC).symm
      · rw [hL] at hc
        obtain ⟨u', rfl⟩ := trap_end hc
        exact .inr ⟨m, R₁, (u', π₁), ⟨(servedLog rsO, linkEnd (PUnit.unit, π₁)
          (.ret (.inr PUnit.unit) u')), .inl ⟨rsO, _, _, hRO, hcO, rfl⟩, by rw [hlog]; rfl⟩,
          hv, hf, rfl⟩
    · simp only [Prod.mk.injEq] at hyeq
      obtain ⟨rfl, rfl⟩ := hyeq
      obtain ⟨R₁, π₁⟩ := s₁
      have hnt := noTrap_satP hsat
      obtain ⟨rsO, hRO, hsv, hcase⟩ := rounds_RO hR (fun L₁ z L₂ hL hz => (hnt L₁ z L₂ hL hz).elim)
      rcases hcase with ⟨hlog, hv⟩ | ⟨m, -, -, -, L₁, a', hL⟩
      · have hO := div_RO.1 hsrv
        have hc' := div_log_nil hO
        subst hc'
        refine .inl ⟨R₁, .div, ⟨(servedLog rsO ++ [], .div), .inr (.inl ⟨rsO, _, a, [], hRO,
          by rw [hsv]; exact hsat, hO, rfl⟩), by rw [hlog]; rfl⟩, by simpa using hv, rfl⟩
      · exact (hnt L₁ ⟨a', .inr PUnit.unit⟩ [] hL rfl).elim
    · simp only [Prod.mk.injEq] at hyeq
      obtain ⟨rfl, rfl⟩ := hyeq
      obtain ⟨hO, hv⟩ := inf_RO hinf (noTrap_inf hω)
      exact .inl ⟨(st n).1, .div, ⟨(logTake lg n, .div), .inr (.inr ⟨ω, hω, lg, _, n, hO, hn,
        rfl⟩), rfl⟩, hv n, rfl⟩

/-! ## Productive streams -/

theorem infR_eq (u π : Store Nat) (R : List (sigN l.host.length).Op) (q : Nat × Payload) :
    (HLinked2.realize l.host (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))).2.2 (u, π, R) q =
      (l.linkR P Ie Ii).2.2 ((R, π), u) q := by
  ext ω
  constructor
  · rintro ⟨hω, hv⟩
    rcases hω with ⟨rs, s₁, a, ω', -, -, hω', -⟩ | ⟨ω', hω', lg, st, hinf, hunb, hcoh⟩
    · rw [serverO_inf] at hω'
      exact hω'.elim
    · obtain ⟨stR, hinfR, -⟩ := inf_OR hinf (R := R) (fun k => by
        obtain ⟨R', h⟩ := hv (logTake lg k).length
        rw [hcoh] at h
        exact ⟨R', h⟩)
      exact .inr ⟨ω', hω', lg, stR, hinfR, hunb, hcoh⟩
  · rintro (⟨rs, s₁, a, ω', -, -, hω', -⟩ | ⟨ω', hω', lg, st, hinf, hunb, hcoh⟩)
    · rw [serverR_inf] at hω'
      exact hω'.elim
    · obtain ⟨hO, hv⟩ := inf_RO hinf (noTrap_inf hω')
      refine ⟨.inr ⟨ω', hω', lg, _, hO, hunb, hcoh⟩, fun n => ?_⟩
      obtain ⟨k, hk⟩ := hunb n
      have h1 := hv k
      rw [← hcoh k, HLinkedSessionObj.streamTake_split ω hk] at h1
      obtain ⟨R₁, h₁, -⟩ := HLinkedSessionObj.visRun_split h1
      exact ⟨R₁, h₁⟩

/-! ## Pending calls -/

theorem pendR_eq (hw : l.WireTy) (u π : Store Nat) (R : List (sigN l.host.length).Op)
    (q : Nat × Payload) :
    (HLinked2.realize l.host (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))).2.1 (u, π, R) q =
      (l.linkR P Ie Ii).2.1 ((R, π), u) q := by
  ext x
  constructor
  · rintro (h | ⟨d, m', h, -⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, hk, hm⟩)
    · exact h.elim
    · exact h.elim
    · have hd' : (d, e) ∈ (HLinked2.realize l.host
          (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))).1 (u, π, R) q := hd
      rw [finR_eq] at hd'
      obtain ⟨y, hy, hye⟩ := hd'
      simp only [Prod.mk.injEq] at hye
      obtain ⟨rfl, -⟩ := hye
      rw [← satP_linkR]
      exact .inr (.inr (.inl ⟨y.1, y.2, hy, hc⟩))
    · have hω' : ω ∈ (HLinked2.realize l.host
          (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii))).2.2 (u, π, R) q := hω
      rw [infR_eq] at hω'
      rw [← satP_linkR]
      exact .inr (.inr (.inr ⟨ω, hω', k, hk, hm⟩))
  · rintro ⟨rs, s₁, a, c', hR, hsat, hsats, hx1⟩
    obtain ⟨R₁, π₁⟩ := s₁
    obtain ⟨hc', hroute, hnf⟩ := satP_serverR hsats
    simp only at hc'
    subst hc'
    have hnt := noTrap_satP hsat
    obtain ⟨rsO, hRO, hsv, hcase⟩ := rounds_RO hR (fun L₁ z L₂ hL hz => (hnt L₁ z L₂ hL hz).elim)
    rcases hcase with ⟨hlog, hv⟩ | ⟨m, -, -, -, L₁, a', hL⟩
    swap
    · exact (hnt L₁ ⟨a', .inr PUnit.unit⟩ [] hL rfl).elim
    have hpO : (([] : List (Call (sigN l.host.length))), x.2) ∈
        satP (l.serverO P Ie) (PUnit.unit, π₁) a := by
      refine .inl ?_
      change ([], x.2) ∈ Sum.elim (l.hostPass.2.1 PUnit.unit) ((l.expTripleH P Ie).2.1 π₁)
        (l.route a)
      rw [hroute]
      rfl
    have hxO : x ∈ (l.linkO P Ie Ii).2.1 ((PUnit.unit, π), u) q :=
      ⟨rsO, _, a, [], hRO, by rw [hsv]; exact hsat, hpO, by rw [hx1, hlog]⟩
    obtain ⟨σ, hσ⟩ := refuse_mem hw hxO
    rw [fin_eq hw] at hσ
    have hvx : VisRun l.host R (x.1 ++ [⟨x.2, none⟩]) (x.2 :: R₁) := by
      rw [hx1, List.append_nil]
      exact HLinkedSessionObj.visRun_append hv (.refuse hnf (.nil _))
    have hF : (x.1 ++ [⟨x.2, none⟩], End.ret (Sum.inr PUnit.unit) σ) ∈
        (mapStore HLinked2.storeEquiv (l.linkO P Ie Ii)).1 (u, π) q := hσ
    exact .inr (.inr (.inl ⟨x.1 ++ [⟨x.2, none⟩],
      HLinked2.attachR (x.2 :: R₁) (End.ret (Sum.inr PUnit.unit) σ),
      .inl ⟨x.2 :: R₁, End.ret (Sum.inr PUnit.unit) σ, hF, hvx, rfl⟩, none, [], rfl⟩))

/-! ## The triple -/

/-- **The host-realizable triple is the host-realizable generic link**, the stores
reordered. -/
theorem compTripleR_eq_linkR (hw : l.WireTy) :
    HLinked2.compTripleR P l Ie Ii = mapStore (HLinked2.storeEquivR l.host) (l.linkR P Ie Ii) := by
  rw [compTripleR_eq_realize_linkS hw]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext s q
    obtain ⟨u, π, R⟩ := s
    exact finR_eq u π R q
  · funext s q
    obtain ⟨u, π, R⟩ := s
    exact pendR_eq hw u π R q
  · funext s q
    obtain ⟨u, π, R⟩ := s
    exact infR_eq u π R q

theorem compTripleS_eq_linkR (hw : l.WireTy) :
    HLinked2.compTripleS P l Ie Ii =
      mapStore (HLinked2.storeEquivR l.host)
        (StratLegal.restrict (HLinked2.hostLegal l.host) (l.linkR P Ie Ii)) := by
  rw [HLinked2.compTripleS, compTripleR_eq_linkR hw, restrict_mapStore]

theorem compSession_eq_threadS_linkR (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    HLinked2.compSession P l =
      threadS (StratLegal.restrict (HLinked2.hostLegal l.host) (l.linkR P Ie Ii))
        (([], Ie.store), Ii.store) := by
  have h : ∃ Ie Ii : ScalarInstance, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii :=
    ⟨Ie, Ii, hIe, hIi⟩
  rw [HLinked2.compSession, dite_eq_left_of_eq_true (eq_true h)]
  obtain rfl := NumModule.IsInst.unique h.choose_spec.choose_spec.1 hIe
  obtain rfl := ImpModule.IsInst.unique h.choose_spec.choose_spec.2 hIi
  rw [compTripleS_eq_linkR hw]
  exact threadS_mapStore (HLinked2.storeEquivR l.host) _ (([], h.choose.store), _)

/-! ## Composition of sessions -/

theorem noPlainTrap_hostTripleR (h : Iface) : NoPlainTrap (hostTripleR h) := by
  rintro R m c (⟨-, hx⟩ | ⟨-, hx⟩ | ⟨p, -, -, hx⟩) <;> simp at hx

theorem retDet_hostTripleR (h : Iface) : RetDet (hostTripleR h) := by
  rintro R m c c' b b' s₁ s₁' h1 h2
  rcases h1 with ⟨hf, h1⟩ | ⟨hf, h1⟩ | ⟨p, hm, hl, h1⟩ <;>
    rcases h2 with ⟨hf', h2⟩ | ⟨hf', h2⟩ | ⟨p', hm', hl', h2⟩ <;>
    simp only [Prod.mk.injEq, End.ret.injEq] at h1 h2 <;>
    obtain ⟨rfl, rfl, rfl⟩ := h1 <;> obtain ⟨h2c, rfl, rfl⟩ := h2
  · subst h2c; rfl
  · exact absurd hf hf'
  · exact absurd hf (legal_not_forced hm' hl')
  · exact absurd hf' hf
  · subst h2c; exact ⟨rfl, fun _ => rfl⟩
  · subst h2c; exact ⟨rfl, fun hh => absurd (eq_of_heq hh) (by simp)⟩
  · exact absurd hf' (legal_not_forced hm hl)
  · subst h2c; exact ⟨rfl, fun hh => absurd (eq_of_heq hh) (by simp)⟩
  · subst h2c
    refine ⟨rfl, fun hh => ?_⟩
    obtain rfl := Option.some.inj (eq_of_heq hh)
    rfl

theorem noPlainTrap_serverR : NoPlainTrap (l.serverR P Ie) :=
  SessionExt.noPlainTrap_routeS l.route (noPlainTrap_hostTripleR l.host) noPlainTrap_expTripleH

theorem retDet_serverR (o : GrowOracle) : RetDet (l.serverR (profile o) Ie) :=
  SessionExt.retDet_routeS l.route (retDet_hostTripleR l.host) (retDet_expTripleH o)

/-- **The host-realizable server's session is the realizability host beside the exporter's
session**, below the routing handler (`profile o`). -/
theorem threadS_serverR (o : GrowOracle) (R : List (sigN l.host.length).Op) (π : Store Nat) :
    threadS (l.serverR (profile o) Ie) (R, π) =
      ((threadS (hostTripleR l.host) R).pair (threadS (l.expTripleH (profile o) Ie) π)).comp
        (DStrategy.ofHandler (SessionExt.routeH l.route)) :=
  (SessionExt.pair_comp_routeH l.route (noPlainTrap_hostTripleR l.host)
    (retDet_hostTripleR l.host) noPlainTrap_expTripleH (retDet_expTripleH o) R π).symm

/-- **The host-realizable link is the server's session composed with the client's**
(`profile o`). -/
theorem comp_threadS_linkR (o : GrowOracle) (R : List (sigN l.host.length).Op) (π u : Store Nat) :
    (threadS (l.serverR (profile o) Ie) (R, π)).comp (threadS (l.clientH (profile o) Ii) u) =
      threadS (l.linkR (profile o) Ie Ii) ((R, π), u) :=
  SessionLink.comp_threadS noPlainTrap_serverR
    (SessionCat.storeDet_of_retDet (retDet_serverR o))
    (SessionCat.storeDet_of_retDet
      (SessionCat.retDet_linkS (retDet_serverR o) (SimpleI.retDet_impTripleS o))) _ _

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
