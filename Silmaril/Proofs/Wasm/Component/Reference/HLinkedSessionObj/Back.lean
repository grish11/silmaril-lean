module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Fwd

/-!
# Reading rounds of the session object back under a typed host

Along a bisimulation `Rel` of the host-realizable triples relating states with the same refusals
since the last answer, a round of `X` under a typed host `G` (refusing the calls of `R` in its
state, `Refuses`) is a round of the triple of `X`, which the bisimulation transfers to a round of
the triple of `Y`, which is a round of `Y` under the same host, between the same host states
(`round_back`): `Y`'s visible calls are `X`'s, and a call of `Y` whose refusal is hidden is
refused by `G` (it was refused since the last answer, or has no typed answer).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (IsBisim ObsEq RoundEq)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile Thread)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-- A legally answered history on the legal host interface. -/
def legalize {h : Iface} : (c : List (Call (sigN h.length))) →
    (∀ x ∈ c, HLinked2.hostLegal h x.1 x.2) → List (Call (HLinked2.hostSig h))
  | [], _ => []
  | x :: c, hc => ⟨x.1, ⟨x.2, hc x List.mem_cons_self⟩⟩ ::
      legalize c (fun y hy => hc y (List.mem_cons_of_mem _ hy))

theorem map_liftCall_legalize {h : Iface} :
    ∀ (c : List (Call (sigN h.length))) (hc : ∀ x ∈ c, HLinked2.hostLegal h x.1 x.2),
      (legalize c hc).map StratLegal.liftCall = c
  | [], _ => rfl
  | x :: c, hc => by
    simp only [legalize, List.map_cons]
    rw [map_liftCall_legalize c]
    rfl

theorem visRun_legal {h : Iface} {R R' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (hv : HLinked2.VisRun h R c R') :
    ∀ x ∈ c, HLinked2.hostLegal h x.1 x.2 := by
  induction hv with
  | nil => intro x hx; cases hx
  | refuse _ _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · trivial
    · exact ih x hx
  | answer _ hl _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hl
    · exact ih x hx

theorem refuses_visRun {τ : Type} {G : τ → HostFuncId → List RVal → Option (List RVal × τ)}
    {h : Iface} {R R' : List (sigN h.length).Op} {c : List (Call (sigN h.length))}
    (hv : HLinked2.VisRun h R c R') : ∀ {st st' : τ}, Refuses G R st → HostRun G st c st' →
      Refuses G R' st' := by
  induction hv with
  | nil => intro st st' hR hr; cases hr; exact hR
  | @refuse R R' m c _ _ ih =>
    intro st st' hR hr
    cases hr with
    | cons hd hr =>
      obtain ⟨k, ws, hm, hA⟩ := hd
      obtain ⟨hg, rfl⟩ := hA
      refine ih (fun x hx => ?_) hr
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨k, ws, hm, hg⟩
      · exact hR x hx
  | answer _ _ _ ih =>
    intro st st' hR hr
    cases hr with
    | cons _ hr => exact ih (fun _ h => (List.not_mem_nil h).elim) hr

theorem realRun_vis {h : Iface} {R R' : List (sigN h.length).Op}
    {A : List (Call (sigN h.length))} (hA : AllAns A) (hr : HLinked2.RealRun h R A R') :
    HLinked2.VisRun h R A R' := by
  induction hr with
  | nil => exact .nil _
  | forced _ _ _ =>
    obtain ⟨_, _, _, he⟩ := hA _ List.mem_cons_self
    cases he
  | refuse _ _ _ =>
    obtain ⟨_, _, _, he⟩ := hA _ List.mem_cons_self
    cases he
  | answer hm hl _ ih => exact .answer hm hl (ih fun x hx => hA x (List.mem_cons_of_mem _ hx))

theorem visRun_append {h : Iface} {R R₁ R₂ : List (sigN h.length).Op}
    {A B : List (Call (sigN h.length))} (hA : HLinked2.VisRun h R A R₁)
    (hB : HLinked2.VisRun h R₁ B R₂) : HLinked2.VisRun h R (A ++ B) R₂ := by
  induction hA with
  | nil => exact hB
  | refuse hF _ ih => exact .refuse hF (ih hB)
  | answer hm hl _ ih => exact .answer hm hl (ih hB)

theorem outAns_inj' {o o' : Option (List IVal)} (h : outAns o = outAns o') : o = o' := by
  cases o <;> cases o' <;> simp_all [outAns]

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst}

/-- **A round under a typed host transfers along a bisimulation.** -/
theorem round_back {P : Profile} {τ : Type}
    {G : τ → HostFuncId → List RVal → Option (List RVal × τ)} (hT : X.HostTyped G)
    {Rel : X.St → X.St → Prop}
    (hB : IsBisim (HLinked2.compTripleS P X IeX IiX)
      (HLinked2.compTripleS P ⟨eY, iY, wY, X.host⟩ IeY IiY) Rel)
    (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    {u π u' π' : Store Nat} {R : List (sigN X.host.length).Op}
    (hRel : Rel (u, π, R) (u', π', R)) {st st₁ : τ} (hRef : Refuses G R st)
    {j : Fin X.imp.exports.length} {vs : List IVal} {o : Option (List IVal)}
    {H : List (Call (sigN X.host.length))} {u₁ π₁ : Store Nat}
    (htj : ValTy.checkList X.imp.exports[j].ty.params vs = true)
    (r : HLinked2.SessSpec P X IeX IiX u π [(j, vs)] [o] [H] u₁ π₁) (hr : HostRun G st H st₁) :
    ∃ (R₁ : List (sigN X.host.length).Op) (u₁' π₁' : Store Nat)
      (H' : List (Call (sigN X.host.length))),
      Rel (u₁, π₁, R₁) (u₁', π₁', R₁) ∧ Refuses G R₁ st₁ ∧
      HLinked2.SessSpec P ⟨eY, iY, wY, X.host⟩ IeY IiY u' π' [(Fin.cast len j, vs)] [o] [H']
        u₁' π₁' ∧ HostRun G st H' st₁ := by
  have hq : X.toL2.typedQ (j.val, .vals vs) = some (j, vs) := LinkedSessionEquiv.typedQ_typed htj
  have hqY := LinkedSessionEquiv.typedQ_castL hty (j.val, .vals vs)
  rw [hq] at hqY
  simp only [Option.map_some] at hqY
  obtain ⟨R₁, hRR, hRef₁⟩ := realRun_of_hostRun_aux G hT hr R hRef
  obtain ⟨A, T, rfl, hA, hT'⟩ := round_shape r (hostRun_forms hr)
  obtain ⟨RA, hRA, hRT⟩ := realRun_split hRR
  have hvA := realRun_vis hA hRA
  obtain ⟨stA, hrA, hrT⟩ := hostRun_append.1 hr
  -- `X`'s behaviour: its visible calls `c`, its answer `b`, its end refusals
  obtain ⟨c, b, hv, hmemX, hrc, hY⟩ : ∃ (c : List (Call (sigN X.host.length))) (b : Payload ⊕ PUnit.{1}),
      HLinked2.VisRun X.host R c R₁ ∧
      (c, End.ret b (u₁, π₁, R₁)) ∈ HLinked2.compFin P X IeX IiX (u, π, R) (j.val, .vals vs) ∧
      HostRun G st c st₁ ∧ b = outAns o := by
    rcases hT' with rfl | ⟨m, rfl⟩
    · cases hRT
      cases hrT
      refine ⟨A, outAns o, hvA, ?_, hrA, rfl⟩
      simp only [HLinked2.compFin, hq]
      exact .inl ⟨o, u₁, π₁, _, by simpa using r, hvA, rfl⟩
    · have ho := (refuse_last r rfl).2
      subst ho
      cases hrT with
      | cons hd hn =>
        cases hn
        have hd' := hd
        obtain ⟨k, ws, -, hg, rfl⟩ := hd
        cases hRT with
        | forced hF hn =>
          cases hn
          refine ⟨A, outAns none, hvA, ?_, hrA, rfl⟩
          simp only [HLinked2.compFin, hq]
          exact .inr (.inl ⟨m, u₁, π₁, R₁, r, hvA, hF, rfl⟩)
        | refuse hF hn =>
          cases hn
          have hv : HLinked2.VisRun X.host R (A ++ [⟨m, none⟩]) (m :: RA) :=
            visRun_append hvA (.refuse hF (.nil _))
          refine ⟨A ++ [⟨m, none⟩], outAns none, hv, ?_,
            hostRun_append.2 ⟨_, hrA, .cons hd' (.nil _)⟩, rfl⟩
          simp only [HLinked2.compFin, hq]
          exact .inl ⟨none, u₁, π₁, m :: RA, r, hv, rfl⟩
  -- the round on the legal interface and its transfer
  have hl := visRun_legal hv
  obtain ⟨s₁', hmemY, hRel₁⟩ := (hB _ _ hRel).ret (j.val, .vals vs) (legalize c hl) b (u₁, π₁, R₁)
    (by show ((legalize c hl).map StratLegal.liftCall, End.ret b (u₁, π₁, R₁)) ∈
          HLinked2.compFin P X IeX IiX (u, π, R) (j.val, .vals vs)
        rw [map_liftCall_legalize]; exact hmemX)
  change ((legalize c hl).map StratLegal.liftCall, End.ret b s₁') ∈
    HLinked2.compFin P ⟨eY, iY, wY, X.host⟩ IeY IiY (u', π', R) (j.val, .vals vs) at hmemY
  rw [map_liftCall_legalize] at hmemY
  obtain ⟨u₁', π₁', R₁'⟩ := s₁'
  simp only [HLinked2.compFin, hqY] at hmemY
  rcases hmemY with ⟨o', u', π', R', hs, hv', he⟩ | ⟨m', u', π', R', hs, hv', hF', he⟩ |
      ⟨_, _, _, he⟩
  · simp only [End.ret.injEq, Prod.mk.injEq] at he
    obtain ⟨hb, rfl, rfl, rfl⟩ := he
    have ho : o' = o := outAns_inj' (hb.symm.trans hY)
    subst ho
    obtain rfl := visRun_det hv hv'
    exact ⟨R₁, u₁', π₁', c, hRel₁, hRef₁, hs, hrc⟩
  · simp only [End.ret.injEq, Prod.mk.injEq] at he
    obtain ⟨hb, rfl, rfl, rfl⟩ := he
    have ho : o = none := outAns_inj' (hY.symm.trans hb : outAns o = outAns none)
    subst ho
    obtain rfl := visRun_det hv hv'
    refine ⟨R₁, u₁', π₁', c ++ [⟨m', none⟩], hRel₁, hRef₁, hs, ?_⟩
    obtain ⟨k, ws, hk⟩ := valsCalls_round (l := ⟨eY, iY, wY, X.host⟩) hs ⟨m', none⟩ (by simp)
    simp only at hk
    subst hk
    refine hostRun_append.2 ⟨st₁, hrc, .cons ⟨k, ws, rfl, ?_, rfl⟩ (.nil _)⟩
    rcases hF' with hin | hna
    · obtain ⟨k', ws', he', hg⟩ := hRef₁ _ hin
      simp only [Prod.mk.injEq, Payload.vals.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact hg
    · cases hg : G st₁ ⟨k.val⟩ (ws.map toRefVal) with
      | none => rfl
      | some p =>
        obtain ⟨rs, s'⟩ := p
        obtain ⟨us, -, hck⟩ := hT st₁ k.val k.isLt ws rs s' hg
        exact (hna ⟨us, hck⟩).elim
  · cases he

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
