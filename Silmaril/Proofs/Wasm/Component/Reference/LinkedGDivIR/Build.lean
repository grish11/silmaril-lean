module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Back

/-!
# Building the divergences of a linked component with an abstract exporter

Right to left, for the importer diverging host-free (`div_of_roundDivB`) and the exporter's
served call diverging (`div_of_roundDivA`): a session of `g.toExp Ii` from its initial state to
`(u, π)`, then a round from `(u, π)` that diverges in the importer (`RoundDivB`) or in the
exporter (`RoundDivA`), is an IR divergence of `g.toComp.denUD (impSemD P)` after the session on
the pending call.

The proofs are `LinkedSessionDAdeq.div_denD_of_sessDivsB` and `div_denD_of_sessDivsA` with the
exporter's served calls built through `ExpSpec.Adeq` (`expEnvG`, by `fwd`) and its diverging
call through `ExpSpec.AdeqD` (`exp_div_buildG`), and the linked export handler over `sigU`
(`top_buildU`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {g : LinkedG} {Ii : SInst}

/-- An importer round with its import calls renamed to the wired exports, below `splitH`. -/
def wiredNG (d : LayerI g.imp Ii) : CRound sigU sigU :=
  ⟨(d.j.val, .vals d.vs), d.dss.flatten.map (wireRoundG g), d.ans⟩

/-- **The importer's node diverging, through `splitH`** (the converse of the read-back of
`roundDivB_of_nodeDiv`): complete rounds of the importer through the layers and a pending call
on which its IR diverges after the import calls `dss`, all import calls being answered by the
exporter's specification from its initial state, are a divergence from the importer's node. -/
theorem link_div_buildG (he : g.exp.Adeq P) (hw : g.WireTy) {L : List (LayerI g.imp Ii)}
    {j : Fin g.imp.exports.length} {vs : List IVal}
    {dss : List (List (Round (sigN g.imp.imports.length)))}
    (hvB : rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ∈
      (g.imp.toComp.denUD (impSemD P)).div) {π' : g.exp.St}
    (hrun : LinkedG.ExpRun P g g.exp.init ((L.flatMap fun d => d.dss.flatten) ++ dss.flatten)
      π') :
    rplay ((L.map (wiredG (g := g))).map (CRound.hide (E := sigU)))
      (g.exp.comp.exports.length + j.val, .vals vs) [] ∈ g.nodeDivSrc (impSemD P) := by
  have hall := expRunG_wire hrun
  -- the exporter's environment serves all the import calls
  have hexp : twos (((L.flatMap fun d => d.dss.flatten) ++ dss.flatten).map (wireRoundG g)) ∈
      (g.expObs (impSemD P)).plays := by
    rw [expObs_playsG]
    exact expEnvG he hrun
  -- the importer's node forwards them
  have HN : HB (implsH g.exp.comp.exports.length (wireArgsG g)) (L.map LayerI.l₆)
      (L.map wiredNG) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wireG fun x hx =>
      hall x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hx⟩))) .nil
  obtain ⟨uN, huN, hzN⟩ := hb_pend HN (j.val, .vals vs)
    (hrounds_wireG fun x hx => hall x (List.mem_append_right _ hx))
  have hNB : rplay (L.map wiredNG) (j.val, .vals vs) (dss.flatten.map (wireRoundG g)) ∈
      (Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).div := by
    rw [div_impNodeG _ hw]
    exact ⟨uN, _, hzN, huN, hvB⟩
  -- `splitH` and the pairing
  have HS : HC (splitH g.exp.comp.exports.length) (L.map (wiredG (g := g)))
      ((L.map wiredNG).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_pend HS (splitH_shift' g.exp.comp.exports.length j.val (.vals vs))
    (dss.flatten.map (wireRoundG g))
  refine ⟨_, _, zip_serve_pend (L.map (wiredG (g := g))) _ (dss.flatten.map (wireRoundG g)), ?_,
    _, bS, hzS, ⟨rplay_pair_inr
      ((Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).div_mem hNB),
      by rw [halves_rplay_inr]; exact hNB⟩, hbS⟩
  rw [flatMap_wiredG, ← List.map_append]
  exact hexp

/-- **The importer's node and `splitH`, waiting on an import call** (`link_wait_build` for
`LinkedG`). -/
theorem link_wait_buildG {L : List (LayerI g.imp Ii)} {j : Fin g.imp.exports.length}
    {vs : List IVal} {dss : List (List (Round (sigN g.imp.imports.length)))} {k : Nat}
    {ws : List IVal}
    (hvB : rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ++
      [.inl (.ask (k, .vals ws))] ∈ g.imp.toComp.denU (impSem P))
    {w : Fin g.exp.comp.exports.length} (hw : g.wire[k]? = some w.val)
    (hall : ∀ x ∈ (L.flatMap fun d => d.dss.flatten) ++ dss.flatten,
      ∃ w : Fin g.exp.comp.exports.length, g.wire[x.1.1.val]? = some w.val) :
    rplay (L.map (wiredG (g := g))) (g.exp.comp.exports.length + j.val, .vals vs)
      (dss.flatten.map (wireRoundG g)) ++ [.inl (.ask (w.val, .vals ws))] ∈
      (DStrategy.extTop g.expNode.width
        (Node.denD (impSemD P) g.expNode.width g.impNode)).toStrategy := by
  -- the importer's node forwards the import calls
  have HN : HB (implsH g.exp.comp.exports.length (wireArgsG g)) (L.map LayerI.l₆)
      (L.map wiredNG) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wireG fun x hx =>
      hall x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hx⟩))) .nil
  obtain ⟨uN, huN, hzN⟩ := hb_wait HN (j.val, .vals vs)
    (hrounds_wireG fun x hx => hall x (List.mem_append_right _ hx)) (implsH_wireG hw (.vals ws))
  have hNB : rplay (L.map wiredNG) (j.val, .vals vs) (dss.flatten.map (wireRoundG g)) ++
      [.inl (.ask (w.val, .vals ws))] ∈
      (Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).toStrategy := by
    rw [toStrategy_node_denD, forget_impSemD, LinkedG.impNode, Node.den]
    exact ⟨uN, huN, _, hvB, hzN⟩
  -- `splitH` and the pairing
  have HS : HC (splitH g.exp.comp.exports.length) (L.map (wiredG (g := g)))
      ((L.map wiredNG).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_wait HS (splitH_shift' g.exp.comp.exports.length j.val (.vals vs))
    (dss.flatten.map (wireRoundG g)) (w.val, .vals ws)
  exact ⟨_, wplay_pair_inr hNB, bS, hbS, hzS⟩

/-! ## The session's layers -/

/-- **The layers of a session of `g.toExp Ii`**: the session rounds through the importer's
layers, their import calls, and the rounds of the linked environment. -/
theorem session_layers (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) {M : List URound}
    {s : (g.toExp Ii).St} (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) :
    ∃ (ds : List (LinkedG.SessRound g Ii)) (LL : List (LayerI g.imp Ii)),
      (∀ d ∈ ds, d.Ok) ∧ (∀ d ∈ LL, d.Ok hIi) ∧
      Ii.Path P (.idle Ii.store) (cplay (LL.map LayerI.r)) (.idle s.1) ∧
      LinkedG.ExpRun P g g.exp.init (LL.flatMap fun d => d.dss.flatten) s.2 ∧
      (LL.flatMap fun d => d.dss.flatten) = ds.flatMap (fun d => d.dss.flatten) ∧
      (LL.map (wiredG (g := g))).map (CRound.hide (E := sigU)) = (M.map (shiftG g)).map mk0 ∧
      ∀ m ∈ M, m.1.1 < g.imp.exports.length := by
  obtain ⟨ds, hOk, hp, hr, rfl⟩ := rounds_of_run hR
  obtain ⟨LL, hLL, e₁, e₂⟩ := layers_of hi hIi (rel_uG hOk)
  have hcs : (LL.flatMap fun d => d.dss.flatten) = ds.flatMap fun d => d.dss.flatten := by
    have h₁ : (LL.map LayerI.u).flatMap (·.cs) = LL.flatMap fun d => d.dss.flatten := by
      rw [List.flatMap_map]
      rfl
    have h₂ : (ds.map uG).flatMap (·.cs) = ds.flatMap fun d => d.dss.flatten := by
      rw [List.flatMap_map]
      rfl
    rw [← h₁, ← h₂, e₂]
  have e : LL.map (fun d => (⟨(d.j.val, .vals d.vs), d.ans⟩ : URound)) =
      ds.map LinkedG.SessRound.toU := by
    have h₁ : LL.map (fun d => (⟨(d.j.val, .vals d.vs), d.ans⟩ : URound)) =
        (LL.map LayerI.u).map fun u => (⟨(u.q.1.val, u.q.2), u.a⟩ : URound) := by
      rw [List.map_map]
      rfl
    rw [h₁, e₂, List.map_map]
    rfl
  refine ⟨ds, LL, hOk, hLL, ?_, ?_, hcs, ?_, ?_⟩
  · rw [e₁, cplay_rG]
    exact hp
  · rw [hcs]
    exact hr
  · rw [← e, List.map_map, List.map_map, List.map_map]
    rfl
  · intro m hm
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hm
    exact d.j.isLt

/-! ## The theorems -/

/-- **A round of the importer diverging host-free is an IR divergence** (`Adeq` exporter,
importer `Good` and `IsInst`, `WireTy`): a session of `g.toExp Ii` from its initial state to `s`,
then a round from `s` diverging in the importer, is an IR divergence after the session on the
pending call. -/
theorem div_of_roundDivB (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) {M : List URound} {s : (g.toExp Ii).St}
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hB : LinkedG.RoundDivB P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div := by
  obtain ⟨ds, LL, -, hLL, hpL, hrL, -, hM, hlt⟩ := session_layers hi hIi hR
  obtain ⟨d, sB, t, π₁, rfl, rfl, hOkd, hpd, hrd, hdiv⟩ := hB
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOkd
  have hpath : Ii.Path P (.idle Ii.store) (rplay (LL.map LayerI.r) d.f d.cs)
      (.running d.f sB t) := by
    rw [rplay]
    exact path_append hpL hpd
  have hvB := imp_div_build hi hIi hLL hxs hf₁ hf₂ hrel hpath hdiv
  have hX := link_div_buildG he hw hvB (expRunG_append hrL hrd)
  rw [hM, rplay_mk0] at hX
  rw [div_toComp_eq_sources]
  exact .inl (.inr (top_buildU _ hlt hX))

/-- **A round of the exporter's served call diverging is an IR divergence** (`AdeqD` exporter,
importer `Good` and `IsInst`, `WireTy`): a session of `g.toExp Ii` from its initial state to `s`,
then a round from `s` calling out on lifted arguments on which the wired export diverges, is an
IR divergence after the session on the pending call. -/
theorem div_of_roundDivA (hD : g.exp.AdeqD P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {M : List URound} {s : (g.toExp Ii).St}
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hA : LinkedG.RoundDivA P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div := by
  obtain ⟨ds, LL, hOk, hLL, hpL, hrL, hcs, hM, hlt⟩ := session_layers hi hIi hR
  obtain ⟨d, sB, t, π₁, rfl, rfl, hOkd, hpd, hrd,
    e, s', t', nm, ft, ws, w, hpe, hft, hlw, hwk, hdivA⟩ := hA
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOkd
  -- the importer, waiting on the import call
  have hpath : Ii.Path P (.idle Ii.store) (rplay (LL.map LayerI.r) d.f d.cs ++ [.inl (.ask e)])
      (.waiting d.f s' t' e) := by
    rw [rplay]
    exact path_append (path_append hpL hpd) hpe
  have hvB := imp_wait_build hi hIi hLL hxs hf₁ hf₂ hrel hft hlw hpath
  -- the exporter's run, then its diverging call
  have hrun := expRunG_append hrL hrd
  have hWT : ∀ y ∈ (LL.flatMap fun d => d.dss.flatten) ++ d.dss.flatten, WTG g y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · rw [hcs] at hy
      obtain ⟨d', hd', hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨-, -, -, -, hrel'⟩ := hOk d' hd'
      exact wtG_flatten hw hrel' y hy
    · exact wtG_flatten hw hrel y hy
  have hlt' : e.1.val < g.imp.imports.length := (List.getElem?_eq_some_iff.mp hft).1
  obtain ⟨w', hwk', hty⟩ := wiredG_of hw hlt'
  obtain rfl : w' = w := Fin.ext (Option.some.inj (hwk'.symm.trans hwk))
  have hftw : ft = g.exp.comp.exports[w'].ty := by
    rw [hft] at hty
    simpa using hty
  have hckA : ValTy.checkList g.exp.comp.exports[w'].ty.params ws = true :=
    hftw ▸ checkList_of_liftArgs hlw
  have hA := exp_div_buildG hD hrun hWT hckA hdivA
  have htN := link_wait_buildG hvB hwk (expRunG_wire hrun)
  -- the environment serves the import calls, then diverges on the pending one
  have hz := zip_append (zip_serve_pend (E := sigU) (LL.map (wiredG (g := g)))
    (g.exp.comp.exports.length + d.j.val, .vals d.vs) (d.dss.flatten.map (wireRoundG g)))
    (.sync (Ev.ask (w'.val, Payload.vals ws)) .nil)
  rw [List.append_nil, flatMap_wiredG, ← List.map_append] at hz
  have hd : rplay ((LL.map (wiredG (g := g))).map (CRound.hide (E := sigU)))
      (g.exp.comp.exports.length + d.j.val, .vals d.vs) [] ∈ g.envDivSrc (impSemD P) :=
    ⟨_, _, hz, hA, htN⟩
  rw [hM, rplay_mk0] at hd
  rw [div_toComp_eq_sources]
  exact .inl (.inl (top_buildU _ hlt hd))

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
