module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Exp

/-!
# An IR divergence of the exporter's environment is a `DivA` round

`sessDivsA_of_envDiv`: an IR divergence from the exporter's environment (`envDivSrc`) after a
typed session and a typed pending call is a specification session followed by a round of the
importer waiting on an import call, whose wired export of the exporter diverges:

* the exporter's environment diverges at a pending question (`expObs_div_shape`), so the
  importer's node above it waits on that question (`wait_of_zip_run`), and the environment
  served the earlier import calls (`serve_wait`);
* the outer handlers give the session's rounds and the pending call (`top_div`);
* `splitH`, the pairing and the importer's node forward the pending import call
  (`hc_zip_wait`, `halves_wplay_inr`, `hb_zip_wait`, `implsH_wire`);
* the importer's IR is read back at its waiting position (`imp_wait_readback`);
* the exporter's served rounds and its diverging call are read back along one run of its
  instance (`exp_div_readback`), then split at the session's end (`expRunT_split`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

theorem rplay_snoc_eq {E F : Sig.{0}} (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E))
    (x : Move E F) :
    rplay cl g cs ++ [x] = cplay cl ++ ((.inr (.ask g) :: callMoves cs) ++ [x]) := by
  simp only [rplay, List.append_assoc, List.cons_append]

/-- **An IR divergence from the exporter's environment after a typed session** (under
`Linked2.Adequate`, typed calls and a typed pending call): the session is a specification
session from the instances' stores, and the pending call starts a well-formed round of the
importer, its import calls so far answered by the exporter, then an import call on arguments
that lift at the import's type, on which the wired export of the exporter diverges from the
store the exporter's run reached. -/
theorem sessDivsA_of_envDiv (P : Profile) {l : Linked2} (hl : l.Adequate) {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      l.irDiv (impSemD P) (l.envDivSrc (impSemD P))) :
    outs ∈ Linked2.sessDivsA P l calls j vs := by
  obtain ⟨s, t, u, v, h₁, h₂, hu, ht', d, x, h₃, hd, hx⟩ := h
  obtain ⟨sA, tN, hzA, hsA, htN⟩ := hd
  -- the exporter's environment diverges at a pending question; the node above it waits on it
  obtain ⟨LA, gA, rfl⟩ := expObs_div_shape hsA
  have hpA : Path .idle (twos LA ++ [.inr (.ask gA)] : List (Move sigU sigU)) (.run gA) :=
    (path_twos LA).append (.single (.ask gA))
  obtain ⟨xt, hxt⟩ := (DStrategy.extTop l.expNode.width
    (Node.denD (impSemD P) l.expNode.width l.impNode)).toStrategy.legal htN
  obtain ⟨gd, htw, -⟩ := wait_of_zip_run hzA hpA hxt
  obtain ⟨cl, csP, rfl⟩ := exists_wplay htw
  obtain ⟨hsAe, rfl⟩ := serve_wait noInl_twos_ask hzA
  obtain ⟨hLA, -⟩ := twos_snoc_inj hsAe
  subst hLA
  -- the outer handlers
  obtain ⟨hLd, rfl⟩ := top_div hlen h₁ h₂ hu ht' h₃ rfl hx
  have K : List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl (calls.zip outs) :=
    forall₂_of_map_eq hLd
  have hge : ∀ r ∈ cl, l.exp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨co, hco⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (l.exp.exports.length + co.1.1.val, .vals co.1.2) := congrArg Sigma.fst hco
    rw [h₁]
    exact Nat.le_add_right _ _
  -- `splitH` and the pairing
  obtain ⟨a, ha, b, hb, hz₂⟩ := htN
  rw [expNode_width] at hb
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨xa, hxa⟩ := ((Strategy.id sigU).pair
    (Node.denD (impSemD P) l.expNode.width l.impNode).toStrategy).legal ha
  obtain ⟨f₂, ha₂⟩ := wait_of_zip_top hz₂ hxa hyb (path_wplay _ _ _ _)
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_wait (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at ha
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  obtain ⟨-, -, haN⟩ := ha
  rw [halves_wplay_inr] at haN
  -- the importer's node forwards the pending import call
  rw [toStrategy_node_denD, forget_impSemD, Linked2.impNode, Node.den] at haN
  obtain ⟨uN, huN, vB, hvB, hzN⟩ := haN
  rw [expNode_width] at huN
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨xv, hxv⟩ := (l.imp.toComp.denU (impSem P)).legal hvB
  obtain ⟨mB, hvw⟩ := wait_of_zip_below hzN hyN hxv (path_wplay _ _ _ _)
  obtain ⟨up₂, cs₂, rfl⟩ := exists_wplay hvw
  obtain ⟨low₂, csP', kN, H₂, H₂', hkN, he₂⟩ :=
    hb_zip_wait (oneShot_implsH _ _) hyN (path_wplay _ _ _ _) hzN
  obtain ⟨hlow₂, -, rfl, -⟩ := rplay_snoc_inj he₂
  subst hlow₂
  have G₂ : List.Forall₂ (fun x c => HBR (implsH l.exp.exports.length (wireArgs l)) x
      (downBy l.exp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂)
  have htop : ∀ x ∈ up₂, TopI l.imp x := by
    intro x hx
    obtain ⟨co, c, hxc, hc, hco⟩ := forall₂_mem_left
      (forall₂_comp G₂ (forall₂_and_right K fun co hco => (List.of_mem_zip hco).1)) x hx
    obtain ⟨cq, ccs, ca⟩ := c
    have hcq : cq = (l.exp.exports.length + co.1.1.val, .vals co.1.2) := congrArg Sigma.fst hc
    subst hcq
    obtain ⟨q, a, cs, cs', rfl, hy, -⟩ := hxc
    cases hy
    refine ⟨co.1.1, co.1.2, ?_, ht _ hco⟩
    show ((l.exp.exports.length + co.1.1.val - l.exp.exports.length, Payload.vals co.1.2) :
      Nat × Payload) = _
    rw [Nat.add_sub_cancel_left]
  -- the importer's IR, waiting
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, e, s', t', nm, ft, ws, F, hpath, hf₁, hf₂, hF, hcs, hft, hlw,
    hmB⟩ :=
    imp_wait_readback hl.impGood hIi htop hck hvB
  subst hmB
  have hlt : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hft).1
  obtain ⟨w, hwk, hty⟩ := wired hl.wireTy hlt
  have e₁ := (implsH_wire hwk (.vals ws)).symm.trans hkN
  obtain ⟨rfl, -⟩ := Prog.call.inj e₁
  have hftw : ft = l.exp.exports[w].ty := by
    rw [hft] at hty
    simpa using hty
  have hckA : ValTy.checkList l.exp.exports[w].ty.params ws = true :=
    hftw ▸ checkList_of_liftArgs hlw
  -- the rounds of the session and the import calls so far
  obtain ⟨ds, hOk, hr, hcsA, hF', hWT⟩ := build_rounds hl.wireTy (forall₂_comp F G₂) K
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_inv hl.wireTy dss.flatten csP H₂'
  have hWTP : ∀ y ∈ dss.flatten, WT l y := by
    intro y hy
    obtain ⟨ds', hds, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨x', hx'⟩ := forall₂_mem_right hF ds' hds
    obtain ⟨nm, ft, ws, hft, hp, hck'⟩ := impRel_typed hx' y hy
    exact wt_of hl.wireTy hft hp hck'
  have hWTall : ∀ y ∈ (ds.flatMap fun d => d.dss.flatten) ++ dss.flatten, WT l y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hWT y hy
    · exact hWTP y hy
  rw [hcsA, hcsP, ← List.map_append] at hsA
  -- the exporter, along one run
  have hLtyped : ∀ x ∈ ((ds.flatMap fun d => d.dss.flatten) ++ dss.flatten).map (wireRound l),
      ∃ (w : Fin l.exp.exports.length) (ws : List IVal),
        x.1 = (w.val, .vals ws) ∧ ValTy.checkList l.exp.exports[w].ty.params ws = true := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w', ws', hw', hp', hck'⟩ := hWTall y hy
    refine ⟨w', ws', ?_, hck'⟩
    show (l.wire.getD y.1.1.val 0, y.1.2) = _
    rw [wire_getD hw', hp']
  obtain ⟨π₁, hS, hdivA⟩ := exp_div_readback hl hIe hLtyped hckA hsA
  have hrun := expRunT_of_sessRounds _ hWTall hS
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunT_split _ _ hrun
  -- the importer's path
  rw [rplay_snoc_eq] at hpath
  obtain ⟨q₁, hp₁, hp₂₃⟩ := path_split_inst hpath
  obtain ⟨u₁, rfl⟩ := idle_of_path_cplay hp₁
  obtain ⟨q₂, hp₂, hp₃⟩ := path_split_inst hp₂₃
  obtain ⟨sB, tB, rfl⟩ : ∃ sB tB, q₂ = .running f sB tB := by
    cases hp₃ with
    | cons t₁ h₁ =>
      cases t₁ with
      | ucall run callout op =>
        cases h₁
        exact ⟨_, _, rfl⟩
  rw [← hr, LinkedSessionIR.cplay_r] at hp₁
  have hSS := sessSpec_of_idle ds calls outs hF' hlen hOk hp₁ hrun₁
  exact ⟨Ie, Ii, u₁, π, hIe, hIi, hSS, ⟨j, vs, f, ics, dss⟩, sB, tB, π₁, rfl, rfl,
    ⟨lowerArgs l.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁, hf₂, hF⟩,
    hp₂, hrun₂, e, s', t', nm, ft, ws, w, hp₃, hft, hlw, hwk, hdivA⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
