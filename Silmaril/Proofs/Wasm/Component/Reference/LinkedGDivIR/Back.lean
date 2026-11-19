module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Layers

/-!
# Reading back the divergences of a linked component with an abstract exporter

Left to right, for the importer's node (`roundDivB_of_nodeDiv`) and the exporter's environment
(`roundDivA_of_envDiv`): after typed rounds `M` of the linked component and a typed pending call
of export `j` on `vs`, an IR divergence from that source is a session of `g.toExp Ii` from its
initial state to a state `(u, π)` from which the call starts a round that diverges in the
importer (`RoundDivB`) or in the exporter's served call (`RoundDivA`).

The proofs are `LinkedSessionDAdeq.sessDivsB_of_nodeDiv` and `sessDivsA_of_envDiv` with the
exporter read back through `ExpSpec.Adeq` (`expEnvG_inv`, then `bwd`) and, for its diverging
call, `ExpSpec.AdeqD` (`exp_div_readbackG`): the served rounds and the diverging call along one
run of the exporter's specification.
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

/-- `run_of_rounds`, ending at the idle state the importer's path reaches. -/
theorem run_of_rounds_idle : ∀ (ds : List (LinkedG.SessRound g Ii)) {u u' : Store Nat}
    {π π' : g.exp.St}, (∀ d ∈ ds, d.Ok) →
    Ii.Path P (.idle u) (ds.flatMap LinkedG.SessRound.instMoves) (.idle u') →
    LinkedG.ExpRun P g π (ds.flatMap fun d => d.dss.flatten) π' →
    (g.toExp Ii).Run P (u, π) (ds.map LinkedG.SessRound.toU) (u', π')
  | [], u, u', π, π', _, hp, hrun => by
    cases hrun
    cases hp
    exact .nil _
  | d :: ds, u, u', π, π', hOk, hp, hrun => by
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunG_split _ _ hrun
    exact .cons (s₁ := (u₁, π₁)) ⟨d, hOk d List.mem_cons_self, hp₁, hr₁, rfl⟩
      (run_of_rounds_idle ds (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂)

/-- The importer's view of the linked rounds below `splitH` are typed export calls. -/
theorem topI_of {M : List URound} (hM : ∀ m ∈ M, TopG g m) {cl : List (CRound sigU sigU)}
    (K : List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M)
    {up₂ : List (CRound sigU sigU)}
    (G₂ : List.Forall₂ (fun x c => HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
      (downBy g.exp.comp.exports.length c)) up₂ cl) :
    ∀ x ∈ up₂, TopI g.imp x := by
  intro x hx
  obtain ⟨m, c, hxc, hc, hm⟩ := forall₂_mem_left
    (forall₂_comp G₂ (forall₂_and_right K fun m hm => hM m hm)) x hx
  obtain ⟨cq, ccs, ca⟩ := c
  have hcq : cq = (g.exp.comp.exports.length + m.1.1, m.1.2) := congrArg Sigma.fst hc
  subst hcq
  obtain ⟨q, a, cs, cs', rfl, hy, -⟩ := hxc
  cases hy
  obtain ⟨j, vs, hjm, hck⟩ := hm
  refine ⟨j, vs, ?_, hck⟩
  show ((g.exp.comp.exports.length + m.1.1 - g.exp.comp.exports.length, m.1.2) :
    Nat × Payload) = _
  rw [Nat.add_sub_cancel_left, hjm]

theorem wtG_flatten (hw : g.WireTy)
    {ics : List (Round Ii.E)} {dss : List (List (Round (sigN g.imp.imports.length)))}
    (hF : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel g.imp Ii) ics dss) :
    ∀ y ∈ dss.flatten, WTG g y := by
  intro y hy
  obtain ⟨ds', hds, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨x', hx'⟩ := forall₂_mem_right hF ds' hds
  obtain ⟨nm, ft, ws, hft, hp, hck'⟩ := impRel_typed hx' y hy
  exact wtG_of hw hft hp hck'

theorem typed_wired {ds : List (Round (sigN g.imp.imports.length))} (h : ∀ y ∈ ds, WTG g y) :
    ∀ r ∈ ds.map (wireRoundG g), g.exp.Typed r := by
  intro r hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  obtain ⟨w, ws, hwy, hp, hck⟩ := h y hy
  refine ⟨w, ws, ?_, hck⟩
  show (g.wire.getD y.1.1.val 0, y.1.2) = _
  rw [wire_getDG hwy, hp]

/-- **An IR divergence from the importer's node after typed rounds** (`Adeq` exporter, importer
`Good` and `IsInst`, `WireTy`, typed rounds and a typed pending call): a session of
`g.toExp Ii`, then a round of the importer diverging host-free. -/
theorem roundDivB_of_nodeDiv (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) {M : List URound} (hM : ∀ m ∈ M, TopG g m) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hck : ValTy.checkList g.imp.exports[j].ty.params vs = true)
    (h : uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈
      g.irDivU (impSemD P) (g.nodeDivSrc (impSemD P))) :
    ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init M s ∧ LinkedG.RoundDivB P g Ii s.1 s.2 j vs := by
  obtain ⟨d, x, h₃, hd, hx⟩ := h
  obtain ⟨sA, tN, hzA, hsA, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := hd
  rw [expObs_playsG] at hsA
  -- the pairing runs, so does the layer above it
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) g.expNode.width g.impNode)).div_run
      ⟨ha, .inr haN⟩
  rw [expNode_widthG] at hb haN
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, htN⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, csP, rfl⟩ := exists_rplay htN
  -- the exporter's environment served all the import calls
  have hAn : NoInl sA := noInl_comp (noInl_ofHandler_pure pure_maskH0) sA hsA
  obtain ⟨rfl, rfl⟩ := serve_run hAn hzA
  -- the linked export handler
  obtain ⟨hLd, rfl⟩ := top_divU hM h₃ rfl hx
  have K : List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M :=
    forall₂_of_map_eq hLd
  have hge : ∀ r ∈ cl, g.exp.comp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨m, hm⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (g.exp.comp.exports.length + m.1.1, m.1.2) := congrArg Sigma.fst hm
    rw [h₁]
    exact Nat.le_add_right _ _
  -- `splitH` and the pairing
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_run (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at haN
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  rw [halves_rplay_inr] at haN
  -- the importer's node
  rw [div_impNodeG _ hw] at haN
  obtain ⟨uN, vB, hzN, huN, hvB⟩ := haN
  obtain ⟨g₂, hvB₂⟩ := (g.imp.toComp.denUD (impSemD P)).div_run hvB
  obtain ⟨up₂, cs₂, rfl⟩ := exists_rplay hvB₂
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨low₂, csP', H₂, H₂', he₂⟩ := hb_zip_run (oneShot_implsH _ _) hyN hzN
  obtain ⟨rfl, rfl, rfl⟩ := rplay_inj he₂
  have G₂ : List.Forall₂ (fun x c => HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
      (downBy g.exp.comp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂)
  have htop := topI_of hM K G₂
  -- the importer's IR
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, sB, tB, F, hpath, hdiv, hf₁, hf₂, hF, hcs⟩ :=
    imp_div_readback hi hIi htop hck hvB
  obtain ⟨ds, hOk, hr, hcsA, hm, hWT⟩ := build_roundsG hw (forall₂_comp F G₂) K
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_invG hw dss.flatten csP H₂'
  have hWTall : ∀ y ∈ (ds.flatMap fun d => d.dss.flatten) ++ dss.flatten, WTG g y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hWT y hy
    · exact wtG_flatten hw hF y hy
  -- the exporter's rounds
  rw [hcsA, hcsP, ← List.map_append] at hsA
  have hU := expEnvG_inv he hsA
  obtain ⟨π', hS⟩ := he.bwd _ (typed_wired hWTall) (by rw [uMoves_eq]; exact hU)
  have hrun := expRun_of_run _ hWTall hS
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunG_split _ _ hrun
  -- the importer's path
  rw [rplay] at hpath
  obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hpath
  obtain ⟨u₁, rfl⟩ := idle_of_path_cplay hp₁
  rw [← hr, cplay_rG] at hp₁
  have hR := run_of_rounds_idle ds hOk hp₁ hrun₁
  rw [hm] at hR
  exact ⟨(u₁, π), hR, ⟨j, vs, f, ics, dss⟩, sB, tB, π', rfl, rfl,
    ⟨lowerArgs g.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁, hf₂, hF⟩,
    hp₂, hrun₂, hdiv⟩

/-- **An IR divergence from the exporter's environment after typed rounds** (`Adeq` and `AdeqD`
exporter, importer `Good` and `IsInst`, `WireTy`, typed rounds and a typed pending call): a
session of `g.toExp Ii`, then a round of the importer calling out on lifted arguments, on which
the wired export diverges from the state the exporter's run reached. -/
theorem roundDivA_of_envDiv (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {M : List URound} (hM : ∀ m ∈ M, TopG g m)
    {j : Fin g.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList g.imp.exports[j].ty.params vs = true)
    (h : uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈
      g.irDivU (impSemD P) (g.envDivSrc (impSemD P))) :
    ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init M s ∧ LinkedG.RoundDivA P g Ii s.1 s.2 j vs := by
  obtain ⟨d, x, h₃, hd, hx⟩ := h
  obtain ⟨sA, tN, hzA, hsA, htN⟩ := hd
  -- the exporter's environment diverges at a pending question; the node above it waits on it
  obtain ⟨LA, gA, rfl⟩ := expObs_div_shapeG hsA
  have hpA : Path .idle (twos LA ++ [.inr (.ask gA)] : List (Move sigU sigU)) (.run gA) :=
    (path_twos LA).append (.single (.ask gA))
  obtain ⟨xt, hxt⟩ := (DStrategy.extTop g.expNode.width
    (Node.denD (impSemD P) g.expNode.width g.impNode)).toStrategy.legal htN
  obtain ⟨gd, htw, -⟩ := wait_of_zip_run hzA hpA hxt
  obtain ⟨cl, csP, rfl⟩ := exists_wplay htw
  obtain ⟨hsAe, rfl⟩ := serve_wait noInl_twos_ask hzA
  obtain ⟨hLA, -⟩ := twos_snoc_inj hsAe
  subst hLA
  -- the linked export handler
  obtain ⟨hLd, rfl⟩ := top_divU hM h₃ rfl hx
  have K : List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M :=
    forall₂_of_map_eq hLd
  have hge : ∀ r ∈ cl, g.exp.comp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨m, hm⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (g.exp.comp.exports.length + m.1.1, m.1.2) := congrArg Sigma.fst hm
    rw [h₁]
    exact Nat.le_add_right _ _
  -- `splitH` and the pairing
  obtain ⟨a, ha, b, hb, hz₂⟩ := htN
  rw [expNode_widthG] at hb ha
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨xa, hxa⟩ := ((Strategy.id sigU).pair
    (Node.denD (impSemD P) g.exp.comp.exports.length g.impNode).toStrategy).legal ha
  obtain ⟨f₂, ha₂⟩ := wait_of_zip_top hz₂ hxa hyb (path_wplay _ _ _ _)
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_wait (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at ha
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  obtain ⟨-, -, haN⟩ := ha
  rw [halves_wplay_inr] at haN
  -- the importer's node forwards the pending import call
  rw [toStrategy_node_denD, forget_impSemD, LinkedG.impNode, Node.den] at haN
  obtain ⟨uN, huN, vB, hvB, hzN⟩ := haN
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨xv, hxv⟩ := (g.imp.toComp.denU (impSem P)).legal hvB
  obtain ⟨mB, hvw⟩ := wait_of_zip_below hzN hyN hxv (path_wplay _ _ _ _)
  obtain ⟨up₂, cs₂, rfl⟩ := exists_wplay hvw
  obtain ⟨low₂, csP', kN, H₂, H₂', hkN, he₂⟩ :=
    hb_zip_wait (oneShot_implsH _ _) hyN (path_wplay _ _ _ _) hzN
  obtain ⟨hlow₂, -, rfl, -⟩ := rplay_snoc_inj he₂
  subst hlow₂
  have G₂ : List.Forall₂ (fun x c => HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
      (downBy g.exp.comp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂)
  have htop := topI_of hM K G₂
  -- the importer's IR, waiting
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, e, s', t', nm, ft, ws, F, hpath, hf₁, hf₂, hF, hcs, hft, hlw,
    hmB⟩ := imp_wait_readback hi hIi htop hck hvB
  subst hmB
  have hlt : e.1.val < g.imp.imports.length := (List.getElem?_eq_some_iff.mp hft).1
  obtain ⟨w, hwk, hty⟩ := wiredG_of hw hlt
  have e₁ := (implsH_wireG hwk (.vals ws)).symm.trans hkN
  obtain ⟨rfl, -⟩ := Prog.call.inj e₁
  have hftw : ft = g.exp.comp.exports[w].ty := by
    rw [hft] at hty
    simpa using hty
  have hckA : ValTy.checkList g.exp.comp.exports[w].ty.params ws = true :=
    hftw ▸ checkList_of_liftArgs hlw
  -- the rounds of the session and the import calls so far
  obtain ⟨ds, hOk, hr, hcsA, hm, hWT⟩ := build_roundsG hw (forall₂_comp F G₂) K
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_invG hw dss.flatten csP H₂'
  have hWTall : ∀ y ∈ (ds.flatMap fun d => d.dss.flatten) ++ dss.flatten, WTG g y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hWT y hy
    · exact wtG_flatten hw hF y hy
  rw [hcsA, hcsP, ← List.map_append] at hsA
  -- the exporter, along one run
  obtain ⟨π₁, hS, hdivA⟩ :=
    exp_div_readbackG he hD (typed_wired hWTall) ⟨w, ws, rfl, hckA⟩ hsA
  have hrun := expRun_of_run _ hWTall hS
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunG_split _ _ hrun
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
  rw [← hr, cplay_rG] at hp₁
  have hR := run_of_rounds_idle ds hOk hp₁ hrun₁
  rw [hm] at hR
  exact ⟨(u₁, π), hR, ⟨j, vs, f, ics, dss⟩, sB, tB, π₁, rfl, rfl,
    ⟨lowerArgs g.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁, hf₂, hF⟩,
    hp₂, hrun₂, e, s', t', nm, ft, ws, w, hp₃, hft, hlw, hwk, hdivA⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
