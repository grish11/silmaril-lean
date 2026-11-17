module

public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Exp
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.BuildA
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Basic

/-!
# The IR divergence law for a simple exporter

`simple_adeqD`: `Simple.expSpec c I` meets `ExpSpec.AdeqD P` at every profile. Its IR component
is `(SimpleI.ofSimple c).toComp` (`SimpleI.toComp_eq`: one core node, no imports), so the
divergence after complete rounds and a pending typed question is the one of
`LinkedSessionDAdeq`, read directly at the component rather than through `Linked2`'s
environment:

* left to right, `imp_div_readback` gives a path of the instance through rounds read back by
  `RdI` to a pending call that diverges host-free; the rounds are a session from the instance's
  store (`sessRounds_of_rdI`, then `run_of_sessRounds`) to a store `π` from which the call
  diverges (`divAt_of_path`), along one run;
* right to left, the session is a path of the instance through the layers (`run_layers`, the
  `ExpSpec.Run` version of `exp_layers`), extended by the pending call, which `imp_div_build`
  turns into a divergence.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {c : Simple} {I : SInst}

/-- **Sessions of a simple exporter as rounds through the layers** (`exp_layers` for
`ExpSpec.Run`): a session of `Simple.expSpec c I` from a well-formed store `s` to `s'` is a path
of complete rounds of the instance from `s` to `s'`, through the layers of `SimpleI.ofSimple c`
(no import calls). -/
theorem run_layers (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ {s s' : Store Nat} {L : List URound}, (Simple.expSpec c I).Run P s L s' →
      I.WellFormed s →
      ∃ M : List (LayerI (SimpleI.ofSimple c) I), (∀ d ∈ M, d.Ok (isInst_ofSimple hI)) ∧
        I.Path P (.idle s) (cplay (M.map LayerI.r)) (.idle s') ∧
        M.map LayerI.l₆ = L.map (mk0 (E := sigU))
  | _, _, _, .nil _, _ => ⟨[], (fun _ h => nomatch h), .nil _, rfl⟩
  | s, _, _, .cons (s₁ := s₁) hstep hrun, hwf => by
    cases hstep with
    | @ret _ j vs ws hj hret =>
      obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem hj)
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
      have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
          c.mod.exports[c.exports[j].core].2.params := by
        rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
        exact lowerList_types _ _ hret.typed
      obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := hret.run
      have steps : Steps P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0)
          ((lowerArgs c.exports[j].ty.params vs).map ofFlat)) (t'.config s₁) :=
        internalP_steps (H := Nat) run
      obtain ⟨wa, hwa⟩ := answer_at hI hwf hk hxs steps (r := .values cvs) final
      have hp₁ : I.Path P (.idle s)
          [.inr (.ask (opAt hI hk hxs)), .inr (.ans (opAt hI hk hxs) wa)] (.idle s₁) :=
        .cons (.call s _) (.cons (.oret run final hwa) (.nil _))
      have hpay : answerPayload wa = some (.flat ys) := by
        rw [answerPayload_of_ofResult? hwa]
        simp only [hys, Option.map_some]
      have hup : (some (Payload.flat ys)).bind (Adapter.up (.lift c.exports[j].ty)) =
          some (.vals ws) := by
        simp only [Option.bind_some, Adapter.up, hws, Option.map_some]
      have hwf' := hret.wellFormed hI (hc.core _ (List.getElem_mem hj)) hwf
      obtain ⟨M, hM, hpM, hmM⟩ := run_layers hc hI hrun hwf'
      let d : LayerI (SimpleI.ofSimple c) I :=
        ⟨⟨opAt hI hk hxs, [], wa⟩, ⟨j, hj⟩, vs, lowerArgs c.exports[j].ty.params vs, hk, [], []⟩
      have hans : d.ans = some (.vals ws) := by
        show (answerPayload wa).bind (Adapter.up (.lift c.exports[j].ty)) = _
        rw [hpay]
        exact hup
      refine ⟨d :: M, ?_, path_append hp₁ hpM, ?_⟩
      · intro d' hd'
        rcases List.mem_cons.mp hd' with rfl | hd'
        · exact ⟨checkLower_of_check hret.typed, rfl, rfl, .nil, .nil⟩
        · exact hM d' hd'
      · rw [List.map_cons, List.map_cons, hmM]
        congr 1
        show (⟨(j, .vals vs), [], d.ans⟩ : CRound sigU sigU) = ⟨(j, .vals vs), [], some (.vals ws)⟩
        rw [hans]
    | @trap _ j vs hj htrap =>
      obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem hj)
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
      have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
          c.mod.exports[c.exports[j].core].2.params := by
        rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
        exact lowerList_types _ _ htrap.typed
      obtain ⟨t', res, run, final, htr⟩ := htrap.run
      have steps : Steps P Det.noHost (invoke s (I.addrs.getD c.exports[j].core 0)
          ((lowerArgs c.exports[j].ty.params vs).map ofFlat)) (t'.config s₁) :=
        internalP_steps (H := Nat) run
      obtain ⟨wa, hwa⟩ := answer_at hI hwf hk hxs steps (r := res) final
      have hp₁ : I.Path P (.idle s)
          [.inr (.ask (opAt hI hk hxs)), .inr (.ans (opAt hI hk hxs) wa)] (.idle s₁) :=
        .cons (.call s _) (.cons (.oret run final hwa) (.nil _))
      have hpay : answerPayload wa = (coreRes res).map .flat := by
        rw [answerPayload_of_ofResult? hwa]
        cases res <;> rfl
      have hwf' := htrap.wellFormed hI (hc.core _ (List.getElem_mem hj)) hwf
      obtain ⟨M, hM, hpM, hmM⟩ := run_layers hc hI hrun hwf'
      let d : LayerI (SimpleI.ofSimple c) I :=
        ⟨⟨opAt hI hk hxs, [], wa⟩, ⟨j, hj⟩, vs, lowerArgs c.exports[j].ty.params vs, hk, [], []⟩
      have hans : d.ans = none := by
        show (answerPayload wa).bind (Adapter.up (.lift c.exports[j].ty)) = _
        rw [hpay]
        exact up_none_of_traps htr
      refine ⟨d :: M, ?_, path_append hp₁ hpM, ?_⟩
      · intro d' hd'
        rcases List.mem_cons.mp hd' with rfl | hd'
        · exact ⟨checkLower_of_check htrap.typed, rfl, rfl, .nil, .nil⟩
        · exact hM d' hd'
      · rw [List.map_cons, List.map_cons, hmM]
        congr 1
        show (⟨(j, .vals vs), [], d.ans⟩ : CRound sigU sigU) = ⟨(j, .vals vs), [], none⟩
        rw [hans]

/-- **The IR divergence law for a simple exporter** (every profile). -/
theorem simple_adeqD (P : Profile) (hc : c.Good) (hI : c.mod.IsInst I) :
    (Simple.expSpec c I).AdeqD P := by
  intro L q hL hq
  obtain ⟨w, ws, rfl, hck⟩ := hq
  have hwl : w.val < c.exports.length := w.isLt.trans_eq (LinkedG.ofSimple_length c)
  have hck' : ValTy.checkList c.exports[w.val].ty.params ws = true := by
    rw [← LinkedG.ofSimple_ty c w.isLt hwl]
    exact hck
  obtain ⟨w', hw'⟩ : ∃ w' : Fin c.exports.length, w'.val = w.val := ⟨⟨w.val, hwl⟩, rfl⟩
  have hck'' : ValTy.checkList c.exports[w'].ty.params ws = true := by
    simp only [Fin.getElem_fin, hw']
    exact hck'
  rw [LinkedG.uMoves_eq, ← rplay_mk0 (E := sigU), ← hw']
  change rplay (L.map mk0) (w'.val, .vals ws) [] ∈
      ((Comp.mk (SimpleI.ofSimple c).imports [(SimpleI.ofSimple c).coreNode]
        (SimpleI.ofSimple c).compExports).denUD (impSemD P)).div ↔ _
  constructor
  · intro h
    have htop : ∀ u ∈ L.map (mk0 (E := sigU)), TopI (SimpleI.ofSimple c) u := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      obtain ⟨v, vs, hq, hv⟩ := hL r hr
      have hvl : v.val < c.exports.length := v.isLt.trans_eq (LinkedG.ofSimple_length c)
      refine ⟨⟨v.val, hvl⟩, vs, hq, ?_⟩
      show ValTy.checkList c.exports[v.val].ty.params vs = true
      rw [← LinkedG.ofSimple_ty c v.isLt hvl]
      exact hv
    obtain ⟨ri, f, ics, dss, sB, tB, G₉, hpath, hdiv, hf₁, hf₂, hF, -⟩ :=
      imp_div_readback (good_ofSimple hc) (isInst_ofSimple hI) htop (j := w') hck'' h
    obtain rfl := impRel_ofSimple_nil hF
    have hpath' : I.Path P (.idle I.store) (cplay ri ++ [.inr (.ask f)]) (.running f sB tB) :=
      hpath
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hpath'
    obtain ⟨π, rfl⟩ := idle_of_path_cplay hp₁
    have hS := sessRounds_of_rdI G₉ hp₁
    rw [toRound_mk0] at hS
    exact ⟨π, LinkedG.run_of_sessRounds hS hL, w', ws, rfl,
      divAt_of_path (c := c) hck'' hf₁ hf₂ hp₂ hdiv⟩
  · rintro ⟨π, hrun, j, vs, hq, hdiv⟩
    obtain ⟨hj, hv⟩ := Prod.mk.inj hq
    cases Payload.vals.inj hv
    obtain rfl : j = w' := Fin.ext hj.symm
    obtain ⟨M, hM, hpM, hmM⟩ := run_layers hc hI hrun hI.1.choose_spec.ok
    obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
    obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
    have hxs : (lowerArgs c.exports[j].ty.params ws).map (·.type) =
        c.mod.exports[c.exports[j].core].2.params := by
      rw [show c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) from hget]
      exact lowerList_types _ _ hdiv.typed
    obtain ⟨g, hg₀, hg⟩ := hdiv.run
    have hpath : I.Path P (.idle I.store) (rplay (M.map LayerI.r) (opAt hI hk hxs) [])
        (.running (opAt hI hk hxs) π (I.initThread (opAt hI hk hxs))) :=
      path_append hpM (.cons (.call π _) (.nil _))
    have hB : Linked2.DivB P π (I.initThread (opAt hI hk hxs)) :=
      ⟨g, by rw [hg₀, initThread_eq (c := c) (j := j) (vs := ws) rfl rfl], hg⟩
    have hv := imp_div_build (good_ofSimple hc) (isInst_ofSimple hI) hM (j := j) (vs := ws)
      (checkLower_of_check hdiv.typed) (f := opAt hI hk hxs) rfl rfl (dss := []) .nil hpath hB
    rw [hmM] at hv
    exact hv

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv
