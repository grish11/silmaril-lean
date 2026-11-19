module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Basic

/-!
# The finished behaviours of the generic link (proofs)

`fin_eq`: the finished behaviours of the open triple (`HLinked2.compFinO`) are those of the
generic link `HLinked2.linkO` (`linkS` of the server and the client), the stores reordered by
`HLinked2.storeEquiv`. An ill-typed question traps at once on both sides. A returning round is a
returning round of the client whose import calls are served by the server (`ExpRunH`, the host
calls the log); the three divergences of `RoundDivC` are the three divergences of `linkS`
(`DivB`: the client diverges; `DivA`: the exporter diverges inside a served wired call;
`Chatter`: a client stream served with finitely many host calls, the prefix of the round extended
over the stream's calls up to the last host call).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
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

/-! ## Bookkeeping -/

theorem sumAns_map_vals (o : Option (List IVal)) :
    ExpSpec.sumAns (o.map Payload.vals) = outAns o := by
  cases o <;> rfl

theorem exists_o_of_ans {j : Fin l.imp.exports.length} {f : Ii.F.Op} (w : Ii.F.Ar f) :
    ∃ o : Option (List IVal), l.imp.liftAns j w = o.map Payload.vals := by
  rcases LinkedSessionEquiv.up_lift_form l.imp.exports[j].ty (answerPayload w) with h | ⟨ws, h⟩
  · exact ⟨none, h⟩
  · exact ⟨some ws, h⟩

/-- `ExpRunT` (no host calls) is `ExpRunH`. -/
theorem expRunH_of_expRunT :
    ∀ {s s' : Store Nat} {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
      Linked2.ExpRunT P l.toL2 Ie s ds s' → HLinked2.ExpRunH P l Ie s ds s'
  | _, _, _, .nil _ => .nil _
  | _, _, _, .ret w hw hr h => .ret w hw hr (expRunH_of_expRunT h)
  | _, _, _, .trap w hw hr h => .trap w hw hr (expRunH_of_expRunT h)

/-- `ExpRunH` without host calls is `ExpRunT`. -/
theorem expRunT_of_expRunH {s s' : Store Nat} {ds : List l.imp.ICall}
    (h : HLinked2.ExpRunH P l Ie s ds s') (hh : l.hostCalls ds = []) :
    Linked2.ExpRunT P l.toL2 Ie s ds s' := by
  induction h with
  | nil => exact .nil _
  | @ret s s₁ s' n ws us ds w hw hr _ ih =>
    rw [show (⟨(n, .vals ws), some (.vals us)⟩ :: ds : List l.imp.ICall) =
      [⟨(n, .vals ws), some (.vals us)⟩] ++ ds from rfl, hostCalls_append,
      hostCalls_one_wired hw, List.nil_append] at hh
    exact .ret w hw hr (ih hh)
  | @trap s s₁ s' n ws ds w hw hr _ ih =>
    rw [show (⟨(n, .vals ws), none⟩ :: ds : List l.imp.ICall) =
      [⟨(n, .vals ws), none⟩] ++ ds from rfl, hostCalls_append,
      hostCalls_one_wired hw, List.nil_append] at hh
    exact .trap w hw hr (ih hh)
  | @host s s' n p R ds i hi _ _ =>
    rw [show (⟨(n, p), R⟩ :: ds : List l.imp.ICall) = [⟨(n, p), R⟩] ++ ds from rfl,
      hostCalls_append, hostCalls_one_host i hi] at hh
    cases hh

theorem hostCalls_of_expRunT :
    ∀ {s s' : Store Nat} {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
      Linked2.ExpRunT P l.toL2 Ie s ds s' → l.hostCalls ds = []
  | _, _, _, .nil _ => rfl
  | _, _, _, .ret (k := k) (ws := ws) (us := us) (ds := ds) w hw _ h => by
    rw [show (⟨(k, .vals ws), some (.vals us)⟩ :: ds : List l.imp.ICall) =
      [⟨(k, .vals ws), some (.vals us)⟩] ++ ds from rfl, hostCalls_append,
      hostCalls_one_wired hw, hostCalls_of_expRunT h]
    rfl
  | _, _, _, .trap (k := k) (ws := ws) (ds := ds) w hw _ h => by
    rw [show (⟨(k, .vals ws), none⟩ :: ds : List l.imp.ICall) =
      [⟨(k, .vals ws), none⟩] ++ ds from rfl, hostCalls_append,
      hostCalls_one_wired hw, hostCalls_of_expRunT h]
    rfl

theorem logTake_of_log {ω : ℕ → Call sigS} {lg : ℕ → List (Call (sigN l.host.length))}
    (h : ∀ k, lg k = logOf l (ω k)) (n : ℕ) :
    logTake lg n = (streamTake ω n).flatMap (logOf l) := by
  simp [logTake, streamTake, h, List.flatMap, List.map_ofFn, Function.comp_def]

theorem logTake_stable {E : Sig.{0}} {lg : ℕ → List (Call E)} {n : ℕ}
    (hn : ∀ k, n ≤ k → lg k = []) : ∀ m, logTake lg (n + m) = logTake lg n
  | 0 => rfl
  | m + 1 => by
    have ih := logTake_stable hn m
    simp only [logTake, streamTake] at ih ⊢
    rw [show n + (m + 1) = (n + m) + 1 by omega, List.ofFn_succ_last]
    simp only [List.flatten_append, Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil, hn (n + m) (by omega)]
    exact ih

theorem servedLog_ofFn {E : Sig.{0}} {A B : Type} {ω : ℕ → Call (sig1 A B)}
    {lg : ℕ → List (Call E)} (n : ℕ) :
    servedLog (List.ofFn fun i : Fin n => ((ω i).1, lg i, (ω i).2)) = logTake lg n := by
  simp [servedLog, logTake, streamTake, List.flatMap, List.map_ofFn, Function.comp_def]

theorem streamTake_wire {L : List l.imp.ICall} {y : ℕ → l.imp.ICall} (M : ℕ) :
    streamTake (Shape.streamAppend (l.imp.wireLog l.wireH L) fun k => l.imp.wireCall l.wireH (y k))
        ((l.imp.wireLog l.wireH L).length + M) =
      l.imp.wireLog l.wireH (L ++ (List.ofFn fun i : Fin M => [y i]).flatten) := by
  rw [LinkedGLink.streamTake_streamAppend, LinkedGLink.flatten_ofFn_singleton,
    LinkedGLink.wireLog_append]
  simp [SimpleI.wireLog, streamTake, List.map_ofFn, Function.comp_def]

/-! ## Typed wired calls -/

theorem expTypedQ_of_wired (hw : l.WireTy) {k : Nat} {nm : String} {ft : FuncTy}
    {xs : List Flat} {ws : List IVal} {w : Fin l.exp.exports.length}
    (himp : l.imp.imports[k]? = some (nm, ft)) (hl : liftArgs ft.params xs = some ws)
    (hwire : l.wire[k]? = some w.val) : (Simple.expSpec l.exp Ie).TypedQ (w.val, .vals ws) := by
  obtain ⟨x, hx, hty⟩ := hw.ty k w.val hwire
  rw [List.getElem?_eq_getElem w.isLt] at hx
  have hx' := Option.some.inj hx
  rw [himp] at hty
  simp only [Option.map_some, Option.some.injEq] at hty
  refine expTypedQ w.isLt ?_
  rw [hx', ← hty]
  exact checkList_of_liftArgs hl

theorem imports_length (hw : l.WireTy) :
    l.imp.imports.length = l.wire.length + l.host.length := by
  have h := congrArg List.length hw.shape.1
  rw [List.length_drop] at h
  have := hw.shape.2
  omega

/-! ## The finished behaviours -/

/-- **The finished behaviours of the open triple are those of the generic link**, the stores
reordered. -/
theorem fin_eq (hw : l.WireTy) (u π : Store Nat) (q : Nat × Payload) :
    HLinked2.compFinO P l Ie Ii (u, π) q =
      (fun x => (x.1, SessionLinkAssoc.mapEnd HLinked2.storeEquiv x.2)) ''
        (l.linkO P Ie Ii).1 ((PUnit.unit, π), u) q := by
  ext ⟨c, e⟩
  rcases hq : l.toL2.typedQ q with _ | ⟨j, vs⟩
  · -- an ill-typed question
    have hnt := typedQ_none hq
    simp only [HLinked2.compFinO, hq]
    constructor
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      cases hx
      exact ⟨([], .ret (.inr PUnit.unit) ((PUnit.unit, π), u)),
        .inl ⟨[], (PUnit.unit, π), .ret (.inr PUnit.unit) u, .nil _, .inl ⟨hnt, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨x', hx', hx⟩
      rcases hx' with ⟨rs, s₁, e', hR, hc, rfl⟩ | ⟨rs, s₁, a, c', hR, hsat, -, -⟩ |
        ⟨ω, hω, -⟩
      · rcases hc with ⟨-, hc⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, -⟩
        · simp only [Prod.mk.injEq] at hc
          obtain ⟨hc, rfl⟩ := hc
          have hrs : rs = [] := List.map_eq_nil_iff.1 hc
          subst hrs
          cases hR
          simp only [Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          rfl
        · exact (hnt (LinkedGLink.typedQ_of_lowered hlow)).elim
      · obtain ⟨j, vs, f, cs, dss, s, t, e'', s', t', nm, ft, ws, rfl, hlow, -⟩ :=
          LinkedGLink.satP_impTripleS_subset (b := l.imp) (wire := l.wireH) _ _ hsat
        exact (hnt (LinkedGLink.typedQ_of_lowered hlow)).elim
      · obtain ⟨j, vs, f, cs, dss, s, t, r, cc, y, rfl, hlow, -⟩ := hω
        exact (hnt (LinkedGLink.typedQ_of_lowered hlow)).elim
  · obtain ⟨rfl, hck⟩ := LinkedSessionEquiv.typedQ_some hq
    have hT : l.imp.TypedQ (j.val, .vals vs) := ⟨j, vs, rfl, hck⟩
    simp only [HLinked2.compFinO, hq]
    constructor
    · rintro (⟨o, u', π', hs, rfl⟩ | ⟨hd, rfl⟩)
      · -- a returning round
        obtain ⟨d, rfl, rfl, hok, hp, hrun, hans, hH⟩ := HLinkedSessionObj.sessSpec_singleH hs
        obtain ⟨rs, hR, hsv, hlog⟩ := rounds_of_expRunH (u := PUnit.unit)
          (wth_flatten hw (LinkedGLink.lowered_forall₂ hok)) hrun
        refine ⟨(servedLog rs, linkEnd (PUnit.unit, π') (.ret (ExpSpec.sumAns d.ans) u')),
          .inl ⟨rs, _, _, hR, ?_, rfl⟩, ?_⟩
        · rw [hsv]
          exact .inr ⟨d.j, d.vs, d.f, d.cs, d.dss, rfl, hok, rfl, .inl ⟨d.w, u', hp, rfl⟩⟩
        · rw [hlog, hH, hans, sumAns_map_vals]
          rfl
      · obtain ⟨d, s, t, π₁, rfl, rfl, hok, hp, hrun, hH, hdiv⟩ := hd
        obtain ⟨rs, hR, hsv, hlog⟩ := rounds_of_expRunH (u := PUnit.unit)
          (wth_flatten hw (LinkedGLink.lowered_forall₂ hok)) hrun
        rcases hdiv with hB | ⟨e', s', t', nm, ft, ws, w, hpe, himp, hlift, hwire, hds⟩ |
          ⟨qs, cc, ds, st, hq0, hst0, hall⟩
        · -- the importer diverges
          refine ⟨(servedLog rs, linkEnd (PUnit.unit, π₁) .div),
            .inl ⟨rs, _, .div, hR, ?_, rfl⟩, ?_⟩
          · rw [hsv]
            exact .inr ⟨d.j, d.vs, d.f, d.cs, d.dss, rfl, hok, rfl, .inr ⟨s, t, hp, hB, rfl⟩⟩
          · rw [hlog, hH]
            rfl
        · -- the exporter diverges inside a wired call
          have hTy := expTypedQ_of_wired (Ie := Ie) hw himp hlift hwire
          refine ⟨(servedLog rs ++ [], .div),
            .inr (.inl ⟨rs, (PUnit.unit, π₁), (w.val, .vals ws), [], hR, .inl ?_,
              (mem_serverO_inr (route_wired w.isLt _)).2
                ⟨rfl, .div, ⟨rfl, .inr ⟨hTy, .inr ⟨⟨w, ws, rfl, hds⟩, rfl⟩⟩⟩, rfl⟩, rfl⟩), ?_⟩
          · rw [hsv]
            refine ⟨d.j, d.vs, d.f, d.cs, d.dss, s, t, e', s', t', nm, ft, ws, rfl, hok, hp, hpe,
              himp, hlift, ?_⟩
            rw [wireH_getD_wired hwire]
          · rw [List.append_nil, hlog, hH]
            rfl
        · -- chatter
          have hr : ∀ k, Ii.Path P (qs k) (callMoves [cc k]) (qs (k + 1)) := fun k => (hall k).1
          have hp' : Ii.Path P (.idle u) (.inr (.ask d.f) :: callMoves d.cs) (qs 0) := by
            rw [hq0]; exact hp
          have hsing : ∀ k, ∃ y, ds k = [y] := by
            intro k
            rcases LinkedGLink.impRel_cases (hall k).2.1 with ⟨-, htr⟩ |
              ⟨_, _, _, _, _, -, -, h, -⟩
            · exact (LinkedGLink.chain_trap_false hp' hr k htr).elim
            · exact ⟨_, h⟩
          choose y hy using hsing
          have hrel : ∀ k, IRel l.imp Ii (cc k) [y k] := fun k => hy k ▸ (hall k).2.1
          have hT' : ∀ k, Linked2.ExpRunT P l.toL2 Ie (st k) [y k] (st (k + 1)) :=
            fun k => hy k ▸ (hall k).2.2
          have hinf₀ : InfServe (l.serverO P Ie) (PUnit.unit, st 0)
              (fun k => l.imp.wireCall l.wireH (y k)) (fun k => l.hostCalls [y k])
              (fun k => (PUnit.unit, st k)) :=
            ⟨rfl, fun k => round_of_expRunH_single (wth_of_impRel hw (hrel k))
              (expRunH_of_expRunT (hT' k))⟩
          rw [hst0] at hinf₀
          obtain ⟨lg, st', hinf⟩ := LinkedGLink.infServe_rounds hR hinf₀
          rw [hsv] at hinf
          have hlg := infServe_log hinf
          refine ⟨(logTake lg (l.imp.wireLog l.wireH d.dss.flatten).length, .div),
            .inr (.inr ⟨_, ⟨d.j, d.vs, d.f, d.cs, d.dss, s, t, qs, cc, y, rfl, hok, hp, hq0,
              fun k => ⟨hr k, hrel k⟩, rfl⟩, lg, st', _, hinf, ?_, rfl⟩), ?_⟩
          · intro k hk
            obtain ⟨m, rfl⟩ : ∃ m, k = (l.imp.wireLog l.wireH d.dss.flatten).length + m :=
              ⟨k - (l.imp.wireLog l.wireH d.dss.flatten).length, by omega⟩
            rw [hlg, Shape.streamAppend_ge (by omega), Nat.add_sub_cancel_left,
              logOf_wireCall (wth_of_impRel hw (hrel m))]
            exact hostCalls_of_expRunT (hT' m)
          · simp only [Prod.mk.injEq]
            refine ⟨?_, rfl⟩
            rw [logTake_of_log hlg, LinkedGLink.streamTake_streamAppend_lt _ _ le_rfl,
              List.take_length, flatMap_logOf_wireLog (wth_flatten hw (LinkedGLink.lowered_forall₂ hok)),
              hH]
    · rintro ⟨x', hx', hx⟩
      rcases hx' with ⟨rs, s₁, e', hR, hc, rfl⟩ | ⟨rs, s₁, a, c', hR, hsat, hsrv, rfl⟩ |
        ⟨ω, hω, lg, st, n, hinf, hn, rfl⟩
      · rcases hc with ⟨hnt, -⟩ | ⟨j', vs', f, cs, dss, hq', hlow, hlog, hend⟩
        · exact (hnt hT).elim
        simp only [Prod.mk.injEq, Payload.vals.injEq] at hq'
        obtain ⟨hj, rfl⟩ := hq'
        obtain rfl : j' = j := Fin.ext hj.symm
        obtain ⟨hrun, hslog⟩ := expRunH_of_rounds hR dss.flatten
          (wth_flatten hw (LinkedGLink.lowered_forall₂ hlow)) hlog
        obtain ⟨⟨⟩, π₁⟩ := s₁
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        rcases hend with ⟨w, u₁, hp, rfl⟩ | ⟨s, t, hp, hB, rfl⟩
        · -- a returning round
          obtain ⟨o, ho⟩ := exists_o_of_ans (j := j') w
          refine .inl ⟨o, u₁, π₁, ?_, ?_⟩
          · rw [hslog]
            exact .round ⟨j', vs, f, cs, w, dss⟩ hlow hp hrun ho (.nil _ _)
          · show End.ret (ExpSpec.sumAns (l.imp.liftAns j' w)) (u₁, π₁) = _
            rw [ho, sumAns_map_vals]
        · -- the importer diverges
          refine .inr ⟨⟨⟨j', vs, f, cs, dss⟩, s, t, π₁, rfl, rfl, hlow, hp, hrun, hslog.symm,
            .inl hB⟩, rfl⟩
      · -- the exporter diverges inside a served call
        obtain ⟨j', vs', f, cs, dss, s, t, e', s', t', nm, ft, ws, hq', hlow, hp, hpe, himp, hlift,
          hxa⟩ := LinkedGLink.satP_impTripleS_subset (b := l.imp) (wire := l.wireH) _ _ hsat
        simp only [Prod.mk.injEq, Payload.vals.injEq] at hq' hxa
        obtain ⟨hj, rfl⟩ := hq'
        obtain rfl : j' = j := Fin.ext hj.symm
        obtain ⟨hlog, rfl⟩ := hxa
        obtain ⟨hrun, hslog⟩ := expRunH_of_rounds hR dss.flatten
          (wth_flatten hw (LinkedGLink.lowered_forall₂ hlow)) hlog
        obtain ⟨⟨⟩, π₁⟩ := s₁
        have hk : e'.1.val < l.imp.imports.length := LinkedGLink.lt_of_getElem? himp
        by_cases hlt : e'.1.val < l.wire.length
        · have hwk : l.wire[e'.1.val]? = some l.wire[e'.1.val] := List.getElem?_eq_getElem hlt
          obtain ⟨x, hx', -⟩ := hw.ty _ _ hwk
          have hwN : l.wire[e'.1.val] < l.exp.exports.length := LinkedGLink.lt_of_getElem? hx'
          rw [wireH_getD_wired hwk] at hsrv
          obtain ⟨hc', e0, ⟨-, he0⟩, h2⟩ := (mem_serverO_inr (route_wired hwN _)).1 hsrv
          simp only at hc' h2
          rcases he0 with ⟨-, he⟩ | ⟨-, ⟨R, s'', -, he⟩ | ⟨⟨w, ws', hww, hds⟩, he⟩⟩
          · simp only at he; subst he; cases h2
          · simp only at he; subst he; cases h2
          simp only [Prod.mk.injEq, Payload.vals.injEq] at hww
          obtain ⟨hww, hws⟩ := hww
          subst hws
          simp only [Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          refine .inr ⟨⟨⟨j', vs, f, cs, dss⟩, s, t, π₁, rfl, rfl, hlow, hp, hrun,
            by rw [hc', List.append_nil, hslog], .inr (.inl ⟨e', s', t', nm, ft, ws, w, hpe, himp,
              hlift, by rw [hwk, hww], hds⟩)⟩, rfl⟩
        · have hlen := imports_length hw
          let i : Fin l.host.length := ⟨e'.1.val - l.wire.length, by omega⟩
          have hi : e'.1.val = l.wire.length + i.val := by simp [i]; omega
          rw [hi, wireH_getD_host i] at hsrv
          obtain ⟨n, hn⟩ := (mem_serverO_inl (route_host i _)).1 hsrv
          simp only [Prod.mk.injEq] at hn
          exact absurd hn.2 (by simp)
      · -- chatter
        obtain ⟨j', vs', f, cs, dss, s, t, r, cc, y, hq', hlow, hp, hr0, hall, rfl⟩ := hω
        simp only [Prod.mk.injEq, Payload.vals.injEq] at hq'
        obtain ⟨hj, rfl⟩ := hq'
        obtain rfl : j' = j := Fin.ext hj.symm
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hlg := infServe_log hinf
        set L := (l.imp.wireLog l.wireH dss.flatten).length with hL
        set M := n - L with hM
        have hr : ∀ k, Ii.Path P (r k) (callMoves [cc k]) (r (k + 1)) := fun k => (hall k).1
        have h₀ : Ii.Path P (.idle u) (.inr (.ask f) :: callMoves cs) (r 0) := by
          rw [hr0]; exact hp
        have hch := LinkedGLink.path_chain h₀ hr M
        obtain ⟨s₁, t₁, hrs⟩ := LinkedGLink.path_idle_running hch
        have hlow' := LinkedGLink.lowered_append hlow (cs' := List.ofFn fun i : Fin M => cc i)
          (dss' := List.ofFn fun i : Fin M => [y i]) (LinkedGLink.forall₂_ofFn fun i => (hall i).2)
        have hRL := LinkedGLink.rounds_of_infServe hinf (L + M)
        have hsv : served (List.ofFn fun i : Fin (L + M) => ((Shape.streamAppend
            (l.imp.wireLog l.wireH dss.flatten) (fun k => l.imp.wireCall l.wireH (y k)) i).1, lg i,
            (Shape.streamAppend (l.imp.wireLog l.wireH dss.flatten)
              (fun k => l.imp.wireCall l.wireH (y k)) i).2)) =
            l.imp.wireLog l.wireH (dss ++ List.ofFn fun i : Fin M => [y i]).flatten := by
          rw [LinkedGLink.served_ofFn, List.flatten_append, streamTake_wire]
        obtain ⟨hrun, hslog⟩ := expRunH_of_rounds hRL _
          (wth_flatten hw (LinkedGLink.lowered_forall₂ hlow')) hsv
        have hstep : ∀ k, Linked2.ExpRunT P l.toL2 Ie (st (L + M + k)).2 [y (M + k)]
            (st (L + M + k + 1)).2 := by
          intro k
          have h1 := hinf.step (L + M + k)
          have hm : Shape.streamAppend (l.imp.wireLog l.wireH dss.flatten)
              (fun k => l.imp.wireCall l.wireH (y k)) (L + M + k) =
              l.imp.wireCall l.wireH (y (M + k)) := by
            rw [Shape.streamAppend_ge (by omega)]
            congr 2
            omega
          rw [hm] at h1
          obtain ⟨hrun1, hc1⟩ := expRunH_single_of_round (wth_of_impRel hw (hall (M + k)).2) h1
          rw [hn _ (by omega)] at hc1
          exact expRunT_of_expRunH hrun1 hc1.symm
        refine .inr ⟨⟨⟨j', vs, f, cs ++ List.ofFn fun i : Fin M => cc i,
            dss ++ List.ofFn fun i : Fin M => [y i]⟩, s₁, t₁, (st (L + M)).2, rfl, rfl, hlow',
          by rw [← hrs]; exact hch, hrun, ?_, .inr (.inr ⟨fun k => r (M + k), fun k => cc (M + k),
            fun k => [y (M + k)], fun k => (st (L + M + k)).2, hrs, rfl, fun k => ⟨hr (M + k),
              (hall (M + k)).2, hstep k⟩⟩)⟩, rfl⟩
        rw [← hslog, servedLog_ofFn]
        have := logTake_stable (lg := lg) (n := n) (fun k hk => hn k hk) (L + M - n)
        rw [show n + (L + M - n) = L + M by omega] at this
        exact this

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
