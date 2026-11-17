module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Inf

/-!
# Building chatter for a linked component with an abstract exporter

`chatter_build`: for an exporter meeting `ExpSpec.AdeqI`, at every profile, a session of
`g.toExp Ii`, then a round of chatter (`RoundDivC`), is an IR divergence from `chatterSrc`. This is
`LinkedSessionDAdeq.chatterSrc_of_sessDivsC` with the exporter's infinite play taken from
`AdeqI` (`exp_env_infG`) instead of `exp_env_inf`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Abstract.InstSession (spullD instSession)
open Silmaril.Wasm.Abstract.NodeDiv (stream)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "pS" => Silmaril.Wasm.Abstract.NodeDiv.prependStream

variable {P : Profile} {g : LinkedG} {Ii : SInst}

theorem expRunG_nil_inv {s s' : g.exp.St} (h : LinkedG.ExpRun P g s [] s') : s' = s := by
  cases h
  rfl

/-- **The exporter's runs, one after another** (`expRunT_prepend` for `LinkedG.ExpRun`). -/
theorem expRunG_prepend :
    ∀ (L : List (List (Round (sigN g.imp.imports.length)))) {s s' : g.exp.St}
      (ds : ℕ → List (Round (sigN g.imp.imports.length))) (st : ℕ → g.exp.St),
      LinkedG.ExpRun P g s L.flatten s' → st 0 = s' →
      (∀ k, LinkedG.ExpRun P g (st k) (ds k) (st (k + 1))) →
      ∃ S : ℕ → g.exp.St, S 0 = s ∧ ∀ k, LinkedG.ExpRun P g (S k) (pS L ds k) (S (k + 1))
  | [], _, _, ds, st, h, h0, hk => by
    obtain rfl := expRunG_nil_inv h
    exact ⟨st, h0, fun k => by rw [pS_nil']; exact hk k⟩
  | x :: L, s, _, ds, st, h, h0, hk => by
    rw [List.flatten_cons] at h
    obtain ⟨s₁, h₁, h₂⟩ := expRunG_split _ _ h
    obtain ⟨S, hS0, hS⟩ := expRunG_prepend L ds st h₂ h0 hk
    refine ⟨fun k => Nat.casesOn k s fun k => S k, rfl, fun k => ?_⟩
    cases k with
    | zero =>
      rw [pS_zero]
      show LinkedG.ExpRun P g s x (S 0)
      rw [hS0]
      exact h₁
    | succ k =>
      rw [pS_succ]
      exact hS k

/-- A single served call is a step of the exporter. -/
theorem step_of_expRunG {s s' : g.exp.St} {y : Round (sigN g.imp.imports.length)}
    (h : LinkedG.ExpRun P g s [y] s') : g.exp.Step P s (wireRoundG g y) s' := by
  have h' := expRunG_run h
  cases h' with
  | cons hs hr =>
    cases hr
    exact hs

/-- **The importer's node on an infinite pending round** (`node_inf_build` for `LinkedG`). -/
theorem node_inf_buildG {L : List (LayerI g.imp Ii)} {j : Fin g.imp.exports.length}
    {vs : List IVal} {Y : ℕ → Round (sigN g.imp.imports.length)}
    (hvI : (rch (L.map LayerI.l₆) (j.val, .vals vs) fun k => (Y k).forget).lim ∈
      (g.imp.toComp.denUD (impSemD P)).inf)
    (hall : ∀ x ∈ L.flatMap fun d => d.dss.flatten,
      ∃ w : Fin g.exp.comp.exports.length, g.wire[x.1.1.val]? = some w.val)
    (hY : ∀ k, ∃ w : Fin g.exp.comp.exports.length, g.wire[(Y k).1.1.val]? = some w.val) :
    (rch (L.map wiredNG) (j.val, .vals vs) fun k => wireRoundG g (Y k)).lim ∈
      (Node.denD (impSemD P) g.expNode.width g.impNode).inf := by
  have HN : HB (implsH g.exp.comp.exports.length (wireArgsG g)) (L.map LayerI.l₆)
      (L.map wiredNG) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wireG fun x hx =>
      hall x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)) .nil
  have h := inf_below_pend (oneCall_implsH _ _) HN (j.val, .vals vs)
    (X := fun k => (Y k).forget) (Y := fun k => wireRoundG g (Y k))
    (fun k => hrounds_wireG (ds := [Y k]) fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact hY k) hvI
  rw [LinkedG.impNode, Node.denD, expNode_widthG]
  exact h

theorem route_cplay_wiredG : ∀ L : List (LayerI g.imp Ii),
    (cplay (L.map (wiredG (g := g)))).map (splitRoute g.exp.comp.exports.length) =
      cplay ((L.map wiredNG).map (CRound.inr (F₁ := sigU)))
  | [] => rfl
  | d :: L => by
    simp only [List.map_cons, cplay, wiredG, wiredNG, CRound.inr, List.map_append,
      route_calls, route_cplay_wiredG L, route_ask, route_ans]

theorem route_rplay_wiredG (L : List (LayerI g.imp Ii)) (j : Nat) (p : Payload) :
    (rplay (L.map (wiredG (g := g))) (g.exp.comp.exports.length + j, p) []).map
        (splitRoute g.exp.comp.exports.length) =
      rplay ((L.map wiredNG).map (CRound.inr (F₁ := sigU))) (.inr (j, p)) [] := by
  simp only [rplay, List.map_append, route_cplay_wiredG, List.map_cons, callMoves, List.map_nil,
    route_ask]

/-- **A round of chatter is an IR divergence from chatter** (`AdeqI` exporter, importer `Good`
and `IsInst`, every profile). -/
theorem chatterSrc_of_roundDivC (hI : g.exp.AdeqI P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) {M : List URound} {s : (g.toExp Ii).St}
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hC : LinkedG.RoundDivC P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈
      g.irDivU (impSemD P) (g.chatterSrc (impSemD P)) := by
  obtain ⟨-, LL, -, hLL, hp₀, hrun₀, -, hM, hlt⟩ := session_layers hi hIi hR
  obtain ⟨d, sB, t, π₁, rfl, rfl, hOk, hp, hr, q, c, ds, st, hq0, hst0, hk⟩ := hC
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOk
  -- the importer's core import calls, one stream: an infinite play of its read-back session
  have hbot : (rch (LL.map LayerI.r) d.f (pS d.cs c)).lim ∈
      (spullD (instSession Ii P Ii.store)).inf := by
    have hp' := hp
    rw [LinkedG.DivRound.instMoves, refCallMoves_eq] at hp'
    have h₀ := Silmaril.Wasm.Abstract.NodeDiv.mem_inf_spullD_instSession_stream.2
      ⟨s.1, hp₀, Silmaril.Wasm.Abstract.NodeDiv.instInf_of_calls hp' hq0 fun k => by
        have hk' := (hk k).1
        rw [refCallMoves_eq] at hk'
        exact hk'⟩
    have e : stream (cplay (LL.map LayerI.r)) d.f (pS d.cs c) =
        rch (LL.map LayerI.r) d.f (pS d.cs c) := by
      funext n
      simp only [stream, rch, rplay, refCallMoves_eq]
    rw [e] at h₀
    exact h₀
  -- each core call is one component call
  have hrelω : ∀ k, Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii (pS d.cs c k)
      (pS d.dss ds k) :=
    pS_forall₂ hrel fun k => (hk k).2.1
  choose Y hY using fun k => impRel_single (hrelω k) (no_trap_of_inf hbot k)
  have hrelY : ∀ k, Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii (pS d.cs c k) [Y k] :=
    fun k => by
      rw [← hY k]
      exact hrelω k
  -- the importer's IR
  have hvI := imp_inf_pend hi hIi hLL hxs hf₁ hf₂ hrelY hbot
  -- the exporter's runs, one call at a time
  obtain ⟨S₁, hS₁0, hS₁⟩ := expRunG_prepend d.dss ds st hr hst0 fun k => (hk k).2.2
  have hS₁' : ∀ k, LinkedG.ExpRun P g (S₁ k) [Y k] (S₁ (k + 1)) := fun k => by
    rw [← hY k]
    exact hS₁ k
  obtain ⟨S, hS0, hSk⟩ := expRunG_prepend
    ((LL.flatMap fun d => d.dss.flatten).map fun x => [x]) (fun k => [Y k]) S₁
    (by rw [flatten_map_singleton]; exact hrun₀) hS₁0 hS₁'
  have hZ : ∀ k, LinkedG.ExpRun P g (S k)
      [pS (LL.flatMap fun d => d.dss.flatten) Y k] (S (k + 1)) := fun k => by
    have h₁ := hSk k
    rw [pS_map (fun x => [x])] at h₁
    exact h₁
  have hE := exp_env_infG hI hS0 fun k => step_of_expRunG (hZ k)
  -- the importer's node
  have hN := node_inf_buildG hvI (expRunG_wire hrun₀)
    fun k => expRunG_wire (hS₁' k) _ List.mem_cons_self
  -- the chatter
  have hd : rplay ((LL.map (wiredG (g := g))).map (CRound.hide (E := sigU)))
      (g.exp.comp.exports.length + d.j.val, .vals d.vs) [] ∈ g.chatterSrc (impSemD P) := by
    refine ⟨_, hE, _, hN, twos ((LL.flatMap fun d => d.dss.flatten).map (wireRoundG g)),
      rplay (LL.map (wiredG (g := g))) (g.exp.comp.exports.length + d.j.val, .vals d.vs) [],
      ?_, ⟨_, path_rplay _ _ _⟩, ?_, ?_, fun k =>
        ⟨evs (streamTake (fun k => wireRoundG g (Y k)) k), ?_, ?_, ?_⟩⟩
    · have hz := zip_serve_pend (E := sigU) (LL.map (wiredG (g := g)))
        (g.exp.comp.exports.length + d.j.val, .vals d.vs) []
      rw [List.append_nil, flatMap_wiredG] at hz
      exact hz
    · rw [expNode_widthG, route_rplay_wiredG]
      exact side_rplay_inr _ _ _ _
    · rw [expNode_widthG, route_rplay_wiredG, halves_rplay_inr]
      exact (Strategy.id sigU).nil_mem
    · rw [length_evs, length_streamTake]
      omega
    · refine ⟨(LL.flatMap fun d => d.dss.flatten).length + k, ?_⟩
      rw [evs_inr, cch_mk0, streamTake_map (wireRoundG g) Y, streamTake_map (wireRoundG g),
        streamTake_prepend, List.map_append, twos_append]
    · refine ⟨k, ?_⟩
      rw [expNode_widthG, route_rplay_wiredG, halves_rplay_inr, evs_inl]
      rw [← rplay_app, List.nil_append]
      exact List.prefix_refl _
  rw [hM, rplay_mk0] at hd
  exact top_buildU _ hlt hd

/-- **Chatter, built** (`AdeqI` exporter, importer `Good` and `IsInst`, every profile). -/
theorem chatter_build (hI : g.exp.AdeqI P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (L : List URound) (s : (g.toExp Ii).St)
    (j : Fin g.imp.exports.length) (vs : List IVal)
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init L s) (hC : LinkedG.RoundDivC P g Ii s.1 s.2 j vs) :
    uMoves L ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div := by
  rw [div_toComp_eq_sources]
  exact .inr (chatterSrc_of_roundDivC hI hi hIi hR hC)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
