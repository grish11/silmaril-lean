module

public import Silmaril.Wasm.Component.Reference.HLinkedLink.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Link
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Trap
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Filter

/-!
# The server and the client of the generic link: basic facts (proofs)

* **Wiring and routing** (`wireH_getD_wired`, `wireH_getD_host`, `route_wired`, `route_host`):
  a wired import reaches the exporter, a host import `wire.length + i` the host call `i`.
* **Rounds of the server** (`mem_serverO_inl`, `mem_serverO_inr`): a routed host question is one
  host call answered by its answer, the store kept; any other question is a round of the
  exporter's triple, without calls. The log of a round is determined by its question and answer
  (`log_of_mem`, `servedLog_eq`).
* **The server's rounds on the importer's import calls are `ExpRunH`** (`rounds_of_expRunH`,
  `expRunH_of_rounds`): for wired calls on typed values and host calls (`HLinkedSession.WTH`),
  served by the server's rounds, with the host calls as the log.
* **A refused call ends the round in a trap** (`path_refuse`): a core import call answered by a
  trap resumes the thread trapped, which answers the trap (`fill_trap_reach'`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.SessionRoute (callS mapS)
open Silmaril.Games.Abstract.StratSession (pairS pairEndL pairEndR)
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

/-! ## Wiring and routing -/

theorem wireH_getD_wired {k w : Nat} (h : l.wire[k]? = some w) : l.wireH.getD k 0 = w := by
  have hk : k < l.wire.length := LinkedGLink.lt_of_getElem? h
  show (l.wireH[k]?).getD 0 = w
  rw [HLinked2.wireH, List.getElem?_append_left hk, h]
  rfl

theorem wireH_getD_host (i : Fin l.host.length) :
    l.wireH.getD (l.wire.length + i.val) 0 = l.exp.exports.length + i.val := by
  show (l.wireH[l.wire.length + i.val]?).getD 0 = _
  rw [HLinked2.wireH, List.getElem?_append_right (by omega)]
  simp [HLinked2.hostWire]

theorem route_wired {w : Nat} (hw : w < l.exp.exports.length) (p : Payload) :
    l.route (w, p) = .inr (w, p) := by
  unfold HLinked2.route
  split
  · rename_i h
    exact absurd h.1 (Nat.not_le.2 hw)
  · rfl

theorem route_host (i : Fin l.host.length) (p : Payload) :
    l.route (l.exp.exports.length + i.val, p) = .inl (i, p) := by
  have h : l.exp.exports.length ≤ l.exp.exports.length + i.val ∧
      l.exp.exports.length + i.val - l.exp.exports.length < l.host.length := ⟨by omega, by omega⟩
  unfold HLinked2.route
  split
  · simp only [Sum.inl.injEq, Prod.mk.injEq, and_true]
    exact Fin.ext (by simp)
  · contradiction

/-! ## Rounds of the server -/

theorem foldS_inl (x : Payload ⊕ PUnit.{1}) : foldS (Sum.map (Sum.inl (β := Payload)) id x) = x := by
  cases x <;> rfl

theorem foldS_inr (x : Payload ⊕ PUnit.{1}) : foldS (Sum.map (Sum.inr (α := Payload)) id x) = x := by
  cases x <;> rfl

theorem sumAns_optAns (x : Payload ⊕ PUnit.{1}) : ExpSpec.sumAns (optAns x) = x := by
  rcases x with x | ⟨⟩ <;> rfl

theorem optAns_sumAns (R : Option Payload) : optAns (ExpSpec.sumAns R) = R := by
  cases R <;> rfl

/-- The end of an exporter round in the server's store. -/
def expEnd (u : PUnit.{1}) : End (Store Nat) (Payload ⊕ PUnit.{1}) →
    End (PUnit.{1} × Store Nat) (Payload ⊕ PUnit.{1})
  | .ret x s => .ret x (u, s)
  | .trap => .trap
  | .div => .div

theorem serverO_fst (σ : PUnit.{1} × Store Nat) (a : Nat × Payload) :
    (l.serverO P Ie).1 σ a = (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
      (pairS l.hostPass (l.expTripleH P Ie)).1 σ (l.route a) := rfl

/-- **A routed host question is one host call**, answered by its answer, the store kept. -/
theorem mem_serverO_inl {σ : PUnit.{1} × Store Nat} {a : Nat × Payload}
    {m : (sigN l.host.length).Op} (h : l.route a = .inl m)
    {x : List (Call (sigN l.host.length)) × End (PUnit.{1} × Store Nat) (Payload ⊕ PUnit.{1})} :
    x ∈ (l.serverO P Ie).1 σ a ↔ ∃ n, x = ([⟨m, n⟩], .ret (ExpSpec.sumAns n) σ) := by
  obtain ⟨⟨⟩, π⟩ := σ
  rw [serverO_fst, h]
  change x ∈ (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
    ((fun x => (x.1, pairEndL π x.2)) ''
      {x | ∃ n, x = ([⟨m, n⟩], End.ret (ExpSpec.sumAns n) PUnit.unit)}) ↔ _
  constructor
  · rintro ⟨y, ⟨z, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨n, by simp [pairEndL, SessionRoute.mapEnd, foldS_inl]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, by simp [pairEndL, SessionRoute.mapEnd, foldS_inl]⟩

/-- **Any other question is a round of the exporter's triple**, without calls. -/
theorem mem_serverO_inr {σ : PUnit.{1} × Store Nat} {a a' : Nat × Payload}
    (h : l.route a = .inr a')
    {x : List (Call (sigN l.host.length)) × End (PUnit.{1} × Store Nat) (Payload ⊕ PUnit.{1})} :
    x ∈ (l.serverO P Ie).1 σ a ↔
      x.1 = [] ∧ ∃ e, ([], e) ∈ ((Simple.expSpec l.exp Ie).sessTripleS P).1 σ.2 a' ∧
        x.2 = expEnd σ.1 e := by
  obtain ⟨⟨⟩, π⟩ := σ
  rw [serverO_fst, h]
  change x ∈ (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
    ((fun x => (x.1, pairEndR PUnit.unit x.2)) ''
      {x : List (Call (sigN l.host.length)) × End (Store Nat) (Payload ⊕ PUnit.{1}) |
        x.1 = [] ∧ ([], x.2) ∈ ((Simple.expSpec l.exp Ie).sessTripleS P).1 π a'}) ↔ _
  constructor
  · rintro ⟨y, ⟨z, ⟨hz, hm⟩, rfl⟩, rfl⟩
    refine ⟨hz, z.2, hm, ?_⟩
    rcases z with ⟨c, ⟨x, s⟩ | _ | _⟩ <;> simp [pairEndR, SessionRoute.mapEnd, expEnd, foldS_inr]
  · rintro ⟨h1, e, he, h2⟩
    refine ⟨(x.1, pairEndR PUnit.unit e), ⟨([], e), ⟨rfl, he⟩, by rw [h1]⟩, ?_⟩
    rcases x with ⟨c, x₂⟩
    simp only at h1 h2
    subst h1 h2
    rcases e with ⟨x, s⟩ | _ | _ <;> simp [pairEndR, SessionRoute.mapEnd, expEnd, foldS_inr]

/-- The host calls of one served call: its host call with its answer, if routed to the host. -/
def logOf (l : HLinked2) (z : Call sigS) : List (Call (sigN l.host.length)) :=
  match l.route z.1 with
  | .inl m => [⟨m, optAns z.2⟩]
  | .inr _ => []

/-- **The log of a server round is that of its question and answer.** -/
theorem log_of_mem {σ σ' : PUnit.{1} × Store Nat} {a : Nat × Payload} {x : Payload ⊕ PUnit.{1}}
    {c : List (Call (sigN l.host.length))} (h : (c, End.ret x σ') ∈ (l.serverO P Ie).1 σ a) :
    c = logOf l ⟨a, x⟩ := by
  unfold logOf
  rcases hr : l.route a with m | a'
  · obtain ⟨n, hn⟩ := (mem_serverO_inl hr).1 h
    simp only [Prod.mk.injEq, End.ret.injEq] at hn
    obtain ⟨rfl, rfl, -⟩ := hn
    simp [optAns_sumAns]
  · exact ((mem_serverO_inr hr).1 h).1

theorem servedLog_eq {σ σ' : PUnit.{1} × Store Nat}
    {rs : List ((Nat × Payload) × List (Call (sigN l.host.length)) × (Payload ⊕ PUnit.{1}))}
    (h : Rounds (l.serverO P Ie) σ rs σ') : servedLog rs = (served rs).flatMap (logOf l) := by
  induction h with
  | nil => rfl
  | @cons s s₁ s₂ a c b rs hr _ ih =>
    simp only [servedLog, served, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [log_of_mem hr, ih]

/-- The log of an infinite service is that of its calls. -/
theorem infServe_log {σ : PUnit.{1} × Store Nat} {ω : ℕ → Call sigS}
    {lg : ℕ → List (Call (sigN l.host.length))} {st : ℕ → PUnit.{1} × Store Nat}
    (h : InfServe (l.serverO P Ie) σ ω lg st) (k : ℕ) : lg k = logOf l (ω k) :=
  log_of_mem (h.step k)

/-! ## Typed questions of the exporter -/

theorem expTypedQ {w : Nat} (hw : w < l.exp.exports.length) {ws : List IVal}
    (hc : ValTy.checkList l.exp.exports[w].ty.params ws = true) :
    (Simple.expSpec l.exp Ie).TypedQ (w, .vals ws) := by
  refine ⟨⟨w, by simpa [SimpleI.toComp, SimpleI.ofSimple] using hw⟩, ws, rfl, ?_⟩
  simpa [SimpleI.toComp, SimpleI.ofSimple] using hc

/-! ## Wired and host calls -/

theorem wireCall_wired {z : l.imp.ICall} {w : Nat} (h : l.wire[z.1.1.val]? = some w) :
    l.imp.wireCall l.wireH z = ⟨(w, z.1.2), ExpSpec.sumAns z.2⟩ := by
  unfold SimpleI.wireCall
  rw [wireH_getD_wired h]

theorem wireCall_host {z : l.imp.ICall} (i : Fin l.host.length)
    (hi : z.1.1.val = l.wire.length + i.val) :
    l.imp.wireCall l.wireH z = ⟨(l.exp.exports.length + i.val, z.1.2), ExpSpec.sumAns z.2⟩ := by
  unfold SimpleI.wireCall
  rw [hi, wireH_getD_host i]

/-- A host call of `WTH`, as an index of the host interface. -/
theorem wth_host {z : l.imp.ICall}
    (h : l.wire.length ≤ z.1.1.val ∧ z.1.1.val - l.wire.length < l.host.length) :
    ∃ i : Fin l.host.length, z.1.1.val = l.wire.length + i.val :=
  ⟨⟨z.1.1.val - l.wire.length, h.2⟩, by simp; omega⟩

/-- **The log of a wired or host call is its host call.** -/
theorem logOf_wireCall {z : l.imp.ICall} (hz : WTH l z) :
    logOf l (l.imp.wireCall l.wireH z) = l.hostCalls [z] := by
  rcases hz with ⟨w, ws, hw, -, -⟩ | hh
  · rw [wireCall_wired hw, hostCalls_one_wired (k := z.1.1) (p := z.1.2) (R₀ := z.2) hw]
    unfold logOf
    rw [route_wired w.isLt]
  · obtain ⟨i, hi⟩ := wth_host hh
    rw [wireCall_host i hi, hostCalls_one_host (k := z.1.1) (p := z.1.2) (R₀ := z.2) i hi]
    unfold logOf
    rw [route_host i]
    simp [optAns_sumAns]

theorem flatMap_logOf_wireLog {ds : List l.imp.ICall} (hg : ∀ z ∈ ds, WTH l z) :
    (l.imp.wireLog l.wireH ds).flatMap (logOf l) = l.hostCalls ds := by
  induction ds with
  | nil => rfl
  | cons z ds ih =>
    rw [show z :: ds = [z] ++ ds from rfl, hostCalls_append, ← ih (fun z hz => hg z (by simp [hz]))]
    simp [SimpleI.wireLog, logOf_wireCall (hg z (by simp))]

/-- **One wired or host call of `ExpRunH` is a round of the server.** -/
theorem round_of_expRunH_single {u : PUnit.{1}} {s s' : Store Nat} {z : l.imp.ICall}
    (hz : WTH l z) (h : HLinked2.ExpRunH P l Ie s [z] s') :
    (l.hostCalls [z], End.ret (l.imp.wireCall l.wireH z).2 (u, s')) ∈
      (l.serverO P Ie).1 (u, s) (l.imp.wireCall l.wireH z).1 := by
  rcases hz with ⟨w, ws, hw, hp, hc⟩ | hh
  · rw [wireCall_wired hw, hostCalls_one_wired (k := z.1.1) (p := z.1.2) (R₀ := z.2) hw]
    refine (mem_serverO_inr (route_wired w.isLt _)).2 ⟨rfl, ?_⟩
    obtain ⟨⟨k, p⟩, R⟩ := z
    simp only at hw hp ⊢
    subst hp
    cases h with
    | ret w' hw' hr hrest =>
      cases hrest
      have hww : w'.val = w.val := by rw [hw] at hw'; exact (Option.some.inj hw').symm
      refine ⟨.ret (ExpSpec.sumAns _) s', ⟨rfl, .inr ⟨expTypedQ w.isLt hc, .inl ⟨_, s',
        ?_, rfl⟩⟩⟩, rfl⟩
      rw [← hww]
      exact .ret w'.isLt hr
    | trap w' hw' hr hrest =>
      cases hrest
      have hww : w'.val = w.val := by rw [hw] at hw'; exact (Option.some.inj hw').symm
      refine ⟨.ret (ExpSpec.sumAns none) s', ⟨rfl, .inr ⟨expTypedQ w.isLt hc, .inl ⟨none, s',
        ?_, rfl⟩⟩⟩, rfl⟩
      rw [← hww]
      exact .trap w'.isLt hr
    | host i hi _ => exact (HLinkedSessionObj.wired_not_host hw i hi).elim
  · obtain ⟨i, hi⟩ := wth_host hh
    rw [wireCall_host i hi, hostCalls_one_host (k := z.1.1) (p := z.1.2) (R₀ := z.2) i hi]
    have hs : s' = s := by
      obtain ⟨⟨k, p⟩, R⟩ := z
      cases h with
      | ret w hw _ _ => exact (HLinkedSessionObj.wired_not_host hw i hi).elim
      | trap w hw _ _ => exact (HLinkedSessionObj.wired_not_host hw i hi).elim
      | host i' hi' hrest => cases hrest; rfl
    subst hs
    exact (mem_serverO_inl (route_host i _)).2 ⟨z.2, rfl⟩

/-- **`ExpRunH` on wired and host calls gives rounds of the server**, with the host calls as the
log. -/
theorem rounds_of_expRunH {u : PUnit.{1}} {π π₁ : Store Nat} {ds : List l.imp.ICall}
    (hg : ∀ z ∈ ds, WTH l z) (h : HLinked2.ExpRunH P l Ie π ds π₁) :
    ∃ rs, Rounds (l.serverO P Ie) (u, π) rs (u, π₁) ∧ served rs = l.imp.wireLog l.wireH ds ∧
      servedLog rs = l.hostCalls ds := by
  induction h with
  | nil s => exact ⟨[], .nil _, rfl, rfl⟩
  | @ret s s₁ s' n ws us ds w hw hr _ ih =>
    obtain ⟨rs, hR, hsv, hlog⟩ := ih (fun z hz => hg z (List.mem_cons_of_mem _ hz))
    have h1 := round_of_expRunH_single (u := u) (hg _ (by simp))
      (.ret w hw hr (.nil s₁) : HLinked2.ExpRunH P l Ie s [⟨(n, .vals ws), some (.vals us)⟩] s₁)
    refine ⟨_ :: rs, .cons h1 hR, ?_, ?_⟩
    · simp [served, SimpleI.wireLog] at hsv ⊢
      exact hsv
    · simp only [servedLog, List.flatMap_cons] at hlog ⊢
      rw [hlog, ← hostCalls_append]
      rfl
  | @trap s s₁ s' n ws ds w hw hr _ ih =>
    obtain ⟨rs, hR, hsv, hlog⟩ := ih (fun z hz => hg z (List.mem_cons_of_mem _ hz))
    have h1 := round_of_expRunH_single (u := u) (hg _ (by simp))
      (.trap w hw hr (.nil s₁) : HLinked2.ExpRunH P l Ie s [⟨(n, .vals ws), none⟩] s₁)
    refine ⟨_ :: rs, .cons h1 hR, ?_, ?_⟩
    · simp [served, SimpleI.wireLog] at hsv ⊢
      exact hsv
    · simp only [servedLog, List.flatMap_cons] at hlog ⊢
      rw [hlog, ← hostCalls_append]
      rfl
  | @host s s' n p R ds i hi _ ih =>
    obtain ⟨rs, hR, hsv, hlog⟩ := ih (fun z hz => hg z (List.mem_cons_of_mem _ hz))
    have h1 := round_of_expRunH_single (u := u) (hg _ (by simp))
      (.host i hi (.nil s) : HLinked2.ExpRunH P l Ie s [⟨(n, p), R⟩] s)
    refine ⟨_ :: rs, .cons h1 hR, ?_, ?_⟩
    · simp [served, SimpleI.wireLog] at hsv ⊢
      exact hsv
    · simp only [servedLog, List.flatMap_cons] at hlog ⊢
      rw [hlog, ← hostCalls_append]
      rfl

/-- **One round of the server serving a wired or host call is one step of `ExpRunH`.** -/
theorem expRunH_single_of_round {σ σ' : PUnit.{1} × Store Nat} {z : l.imp.ICall}
    {c : List (Call (sigN l.host.length))} (hz : WTH l z)
    (h : (c, End.ret (l.imp.wireCall l.wireH z).2 σ') ∈
      (l.serverO P Ie).1 σ (l.imp.wireCall l.wireH z).1) :
    HLinked2.ExpRunH P l Ie σ.2 [z] σ'.2 ∧ c = l.hostCalls [z] := by
  refine ⟨?_, by rw [log_of_mem h, logOf_wireCall hz]⟩
  rcases hz with ⟨w, ws, hw, hp, hc⟩ | hh
  · rw [wireCall_wired hw] at h
    obtain ⟨-, e, he, h2⟩ := (mem_serverO_inr (route_wired w.isLt _)).1 h
    obtain ⟨⟨k, p⟩, R⟩ := z
    simp only at hw hp h2 he
    subst hp
    obtain ⟨-, he⟩ := he
    rcases he with ⟨hnt, -⟩ | ⟨-, ⟨R', s', hst, rfl⟩ | ⟨-, rfl⟩⟩
    · exact (hnt (expTypedQ w.isLt hc)).elim
    · obtain ⟨⟨⟩, π'⟩ := σ'
      simp only [expEnd, End.ret.injEq, Prod.mk.injEq] at h2
      obtain ⟨hR, -, rfl⟩ := h2
      rw [← LinkedGLink.sumAns_inj hR] at hst
      cases hst with
      | ret hj hr => exact .ret w hw hr (.nil _)
      | trap hj hr => exact .trap w hw hr (.nil _)
    · cases h2
  · obtain ⟨i, hi⟩ := wth_host hh
    rw [wireCall_host i hi] at h
    obtain ⟨n, hn⟩ := (mem_serverO_inl (route_host i _)).1 h
    simp only [Prod.mk.injEq, End.ret.injEq] at hn
    obtain ⟨-, -, rfl⟩ := hn
    obtain ⟨⟨k, p⟩, R⟩ := z
    exact .host i hi (.nil _)

/-- **Rounds of the server serving wired and host calls are `ExpRunH`**, the log the host
calls. -/
theorem expRunH_of_rounds {σ σ₁ : PUnit.{1} × Store Nat}
    {rs : List ((Nat × Payload) × List (Call (sigN l.host.length)) × (Payload ⊕ PUnit.{1}))}
    (h : Rounds (l.serverO P Ie) σ rs σ₁) :
    ∀ ds : List l.imp.ICall, (∀ z ∈ ds, WTH l z) → served rs = l.imp.wireLog l.wireH ds →
      HLinked2.ExpRunH P l Ie σ.2 ds σ₁.2 ∧ servedLog rs = l.hostCalls ds := by
  induction h with
  | nil s =>
    intro ds _ hs
    cases ds with
    | nil => exact ⟨.nil _, rfl⟩
    | cons => simp [served, SimpleI.wireLog] at hs
  | @cons s s₁ s₂ a c b rs hr _ ih =>
    intro ds hg hs
    cases ds with
    | nil => simp [served, SimpleI.wireLog] at hs
    | cons z ds =>
      simp only [served, SimpleI.wireLog, List.map_cons, List.cons.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      have hz := hg z (by simp)
      have ha : a = (l.imp.wireCall l.wireH z).1 := by rw [← h1]
      have hb : b = (l.imp.wireCall l.wireH z).2 := by rw [← h1]
      subst ha hb
      obtain ⟨hrun, hc⟩ := expRunH_single_of_round hz hr
      obtain ⟨hrun', hlog⟩ := ih ds (fun z hz => hg z (List.mem_cons_of_mem _ hz)) h2
      refine ⟨?_, ?_⟩
      · have := HLinkedSession.expRunH_append hrun hrun'
        simpa using this
      · simp only [servedLog, List.flatMap_cons] at hlog ⊢
        rw [hlog, hc, ← hostCalls_append]
        rfl

/-! ## Typed questions of the linked component -/

theorem typedQ_none {q : Nat × Payload} (h : l.toL2.typedQ q = none) : ¬ l.imp.TypedQ q := by
  rintro ⟨j, vs, rfl, hc⟩
  rw [LinkedSessionEquiv.typedQ_typed (l := l.toL2) hc] at h
  cases h

theorem typedQ_some_eq {j : Fin l.imp.exports.length} {vs : List IVal} {j' : Fin l.imp.exports.length}
    {vs' : List IVal} (h : l.toL2.typedQ (j'.val, .vals vs') = some (j, vs)) : j' = j ∧ vs' = vs := by
  obtain ⟨he, -⟩ := LinkedSessionEquiv.typedQ_some h
  simp only [Prod.mk.injEq, Payload.vals.injEq] at he
  exact ⟨Fin.ext he.1, he.2⟩

/-! ## Calls of the importer -/

theorem wth_of_impRel (hw : l.WireTy) {x : Σ e : Ii.E.Op, Ii.E.Ar e} {z : l.imp.ICall}
    (h : IRel l.imp Ii x [z]) : WTH l z := by
  rcases LinkedGLink.impRel_cases h with ⟨h, -⟩ | ⟨nm, ft, ws, hk, R, himp, hl, hz, -⟩
  · cases h
  · simp only [List.cons.injEq, and_true] at hz
    subst hz
    exact wth_of hw himp rfl (checkList_of_liftArgs hl)

theorem wth_flatten (hw : l.WireTy) {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
    {dss : List (List l.imp.ICall)} (h : List.Forall₂ (IRel l.imp Ii) cs dss) :
    ∀ z ∈ dss.flatten, WTH l z := by
  induction h with
  | nil => simp
  | @cons x ds cs dss hx _ ih =>
    intro z hz
    rw [List.flatten_cons, List.mem_append] at hz
    rcases hz with hz | hz
    · rcases LinkedGLink.impRel_len hx with rfl | ⟨z', rfl⟩
      · cases hz
      · rw [List.mem_singleton] at hz
        subst hz
        exact wth_of_impRel hw hx
    · exact ih z hz

/-! ## A refused call ends the round in a trap -/

/-- **A core import call answered by a trap is followed by the trap answer.** -/
theorem path_refuse {f : Ii.F.Op} {s s' : Store Nat} {t t' : Silmaril.Wasm.SingleThreaded.Thread}
    {e : Ii.E.Op} (h : Ii.Path P (.running f s t) [.inl (.ask e)] (.waiting f s' t' e)) :
    Ii.Path P (.running f s t) [.inl (.ask e), .inl (.ans e Answer.trap), .inr (.ans f Answer.trap)]
      (.idle s') := by
  cases h with
  | cons h₁ h₂ =>
    cases h₂
    cases h₁ with
    | ucall run callout op =>
      obtain ⟨fr, E, hE⟩ := HLinkedSessionObj.trapped_resume callout
      refine .cons (.ucall run callout op) (.cons (.uret _) ?_)
      have hres : Silmaril.Wasm.SingleThreaded.resumeResult s' t'
          (Answer.toResult (ft := Ii.imports.get e.1) Answer.trap) = .active fr (E.fill [.trap]) :=
        hE
      rw [hres]
      have hb := Silmaril.Proofs.Wasm.Component.Reference.fill_trap_reach' (P := P) s' E fr
      have hfin : Silmaril.Wasm.Game.ResultAt s' (.active fr [.trap]) .trap := rfl
      exact .cons (.oret hb hfin rfl) (.nil _)

/-- **A host import call refused**: the core call answered by a trap, related to the component
call answered `none`. -/
theorem impRel_refuse {e : Ii.E.Op} {nm : String} {ft : FuncTy} {ws : List IVal}
    (himp : l.imp.imports[e.1.val]? = some (nm, ft))
    (hl : liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws) :
    ∃ hk : e.1.val < l.imp.imports.length,
      IRel l.imp Ii ⟨e, Answer.trap⟩ [⟨(⟨e.1.val, hk⟩, .vals ws), none⟩] := by
  have hk : e.1.val < l.imp.imports.length := LinkedGLink.lt_of_getElem? himp
  refine ⟨hk, nm, ft, none, himp, rfl, ?_⟩
  simp only [hl]
  exact ⟨hk, none, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
