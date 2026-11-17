module

public import Silmaril.Wasm.Component.Reference.LinkedGDivIR.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.BuildA
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Main

/-!
# The layers of a linked component with an abstract exporter, for divergences

The layers of `LinkedSessionDAdeq` (`Linked`, `Exp`, `Build`, `BuildA`) for `LinkedG`, over
`sigU` (`Comp.denUD`), with the exporter's facts taken from `ExpSpec.Adeq` and `ExpSpec.AdeqD`
instead of `Simple`'s instance:

* `div_toComp_eq_sources`: the IR divergences over `sigU` are those of the three sources, through
  the linked export handler (`irDivU`);
* `top_divU`, `top_buildU`: the linked export handler on a pending play, both ways;
* `div_impNodeG`: the importer's node has no silent chatter (under `WireTy`);
* the exporter's environment: `expObs_playsG`, `expObs_nodeDivG`, `expObs_div_shapeG`, and its
  divergence read back (`exp_div_readbackG`, by `AdeqD` left to right) and built
  (`exp_div_buildG`, by `AdeqD` right to left) **along one run** of the exporter's
  specification.
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

variable {P : Profile} {g : LinkedG}

/-! ## The sources -/

theorem toComp_eq_nodes (g : LinkedG) :
    g.toComp = Comp.mk [] [g.expNode, g.impNode] g.toComp.exports := rfl

theorem expNode_widthG (g : LinkedG) : g.expNode.width = g.exp.comp.exports.length := rfl

theorem envAfter_linkG (g : LinkedG) :
    envAfter 0 [g.expNode, g.impNode] = g.exp.comp.exports.length + g.imp.exports.length := by
  simp [envAfter, Node.width, LinkedG.expNode, LinkedG.impNode, SimpleI.exports_length_toComp]

/-- **The divergences of a linked component over `sigU`, by source** (every core semantics). -/
theorem div_toComp_eq_sources (C : DCoreSem ImpModule) (g : LinkedG) :
    (g.toComp.denUD C).div =
      g.irDivU C (g.envDivSrc C) ∪ g.irDivU C (g.nodeDivSrc C) ∪
        g.irDivU C (g.chatterSrc C) := by
  rw [toComp_eq_nodes, div_denUD, div_denNodesD, nodesObs_cons, nodesObs_cons, nodesObs_nil]
  simp only [List.length_nil, Nat.zero_add]
  ext p
  constructor
  · rintro ⟨d, x, hz, (hd | hd) | hd, hx⟩
    · exact .inl (.inl ⟨d, x, hz, hd, hx⟩)
    · exact .inl (.inr ⟨d, x, hz, hd, hx⟩)
    · exact .inr ⟨d, x, hz, hd, hx⟩
  · rintro ((⟨d, x, hz, hd, hx⟩ | ⟨d, x, hz, hd, hx⟩) | ⟨d, x, hz, hd, hx⟩)
    · exact ⟨d, x, hz, .inl (.inl hd), hx⟩
    · exact ⟨d, x, hz, .inl (.inr hd), hx⟩
    · exact ⟨d, x, hz, .inr hd, hx⟩

/-! ## The linked export handler -/

/-- **The linked export handler on a pending play**: below it, the environment's pending play is
the rounds shifted to the importer's exports, then the shifted pending question. -/
theorem top_divU {M : List URound} (hM : ∀ m ∈ M, TopG g m) {j : Fin g.imp.exports.length}
    {vs : List IVal} {d x : List (Move sigU sigU)} {Ld : List (Round sigU)} {gd : sigU.Op}
    (h₃ : Zip d x (uMoves M ++ [.inr (.ask (j.val, .vals vs))]))
    (hd : d = twos Ld ++ [.inr (.ask gd)])
    (hx : x ∈ Strategy.ofHandler
      (exportsH (envAfter 0 [g.expNode, g.impNode]) g.toComp.exports)) :
    Ld = M.map (shiftG g) ∧ gd = (g.exp.comp.exports.length + j.val, .vals vs) := by
  subst hd
  rw [envAfter_linkG] at hx
  obtain ⟨yx, hyx⟩ := Strategy.mem_ofHandler.mp hx
  rw [uMoves_eq] at h₃
  obtain ⟨H₂, k₂, hk₂⟩ := hrounds_zip_run (oneShot_implsH _ _) hyx h₃
  refine ⟨hrounds_exportsG_inv g M Ld (fun m hm => ?_) H₂, ?_⟩
  · obtain ⟨j', vs', hq, -⟩ := hM m hm
    rw [hq]
    exact j'.isLt
  · have e := (exportsH_toCompG g j.isLt (.vals vs)).symm.trans hk₂
    exact (Prog.call.inj e).1.symm

/-- **The linked export handler, building a pending play** (the converse of `top_divU`). -/
theorem top_buildU (C : DCoreSem ImpModule) {S : Set (List (Move sigU sigU))} {M : List URound}
    (hM : ∀ m ∈ M, m.1.1 < g.imp.exports.length) {j : Fin g.imp.exports.length} {vs : List IVal}
    (hd : twos (M.map (shiftG g)) ++
      [.inr (.ask (g.exp.comp.exports.length + j.val, .vals vs))] ∈ S) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ g.irDivU C S := by
  have HE : HC (exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports)
      (M.map (mk0 (E := sigU))) ((M.map (shiftG g)).map mk0) := by
    rw [List.map_map]
    refine HC.of_map _ _ M fun m hm => ?_
    obtain ⟨⟨j', p⟩, R⟩ := m
    exact .call (h := exportsH _ _) (q := (j', p))
      (q' := (g.exp.comp.exports.length + j', p)) (k := fun n => .pure n)
      (exportsH_toCompG g (hM _ hm) p) rfl .nil
  obtain ⟨xE, hxE, hzE⟩ := hc_pend HE (exportsH_toCompG g j.isLt (.vals vs)) []
  rw [rplay_mk0, rplay_mk0] at hzE
  rw [uMoves_eq]
  refine ⟨_, xE, hzE, hd, ?_⟩
  rw [envAfter_linkG]
  exact hxE

/-! ## The importer's node -/

/-- **No silent chatter at the importer's node** (under `WireTy`). -/
theorem not_silentChatter_impNodeG (C : DCoreSem ImpModule) (hw : g.WireTy)
    {p : List (Move sigU sigU)} :
    ¬ SilentChatter (implsH g.exp.comp.exports.length (wireArgsG g)) (g.imp.toComp.denUD C) p := by
  rintro ⟨I, hI, t₀, ht₀, ⟨y, hy⟩, hsil, -⟩
  have hinf := (g.imp.toComp.denUD C).inf_isInf hI
  obtain ⟨t₁, ht₁, hlen⟩ := hinf.unbounded (t₀.length + 1)
  have hpre : t₀ <+: t₁ := by
    rcases hinf.total ht₀ ht₁ with h | h
    · exact h
    · have := h.length_le
      omega
  obtain ⟨r, rfl⟩ := hpre
  cases r with
  | nil => simp at hlen
  | cons x r =>
    have hx : t₀ ++ [] ++ [x] ∈ I := hinf.of_prefix ht₁ ⟨r, by simp⟩
    obtain ⟨e, rfl, he⟩ := hsil [] x hx
    have hmem := (g.imp.toComp.denUD C).inf_sub hI hx
    obtain ⟨z, hz⟩ := (g.imp.toComp.denUD C).toStrategy.legal hmem
    rw [List.append_nil] at hz
    obtain ⟨y', hy', hst⟩ := Path.concat_iff.1 hz
    obtain rfl := Path.det hy hy'
    cases hst with
    | call _ m =>
      obtain ⟨r₀, hr₀⟩ := he
      have hlt : m.1 < g.imp.imports.length :=
        lowAsk_denUD C _ _ _ hmem (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨w, hwk, -⟩ := wiredG_of hw hlt
      have e := (implsH_wireG hwk m.2).symm.trans hr₀
      cases e

/-- **The divergences of the importer's node** (under `WireTy`): those of the importer through
its wiring. -/
theorem div_impNodeG (C : DCoreSem ImpModule) (hw : g.WireTy) :
    (Node.denD C g.exp.comp.exports.length g.impNode).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsH g.exp.comp.exports.length (wireArgsG g)) ∧
        v ∈ (g.imp.toComp.denUD C).div} := by
  rw [LinkedG.impNode, div_node_inst]
  ext p
  exact or_iff_left (not_silentChatter_impNodeG C hw)

/-! ## The exporter's environment -/

theorem expObs_playsG (P : Profile) (g : LinkedG) :
    (g.expObs (impSemD P)).plays =
      ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g) := by
  show Silmaril.Wasm.Component.ext 0 _ (Node.denD (impSemD P) 0 g.expNode).toStrategy = _
  rw [toStrategy_node_denD, forget_impSemD, LinkedG.expNode, Node.den]
  rfl

theorem noInl_expNodeDG (P : Profile) (g : LinkedG) :
    ∀ t ∈ (Node.denD (impSemD P) 0 g.expNode).toStrategy, NoInl t := by
  rw [toStrategy_node_denD, forget_impSemD, LinkedG.expNode, Node.den]
  exact noInl_comp (noInl_ofHandler_pure fun _ => ⟨none, rfl⟩)

theorem noInl_expCompG (he : g.exp.Adeq P) :
    ∀ t ∈ (g.exp.comp.denUD (impSemD P)).toStrategy, NoInl t := by
  rw [Reference.toStrategy_denUD_impSemD]
  exact noInl_denU _ he.imports

theorem not_silentChatter_of_nil {M : Type} [CoreModule M] (C : DCoreSem M)
    (h : Handler sigU sigU) {c : Comp M} (hc : c.imports = []) {p : List (Move sigU sigU)} :
    ¬ SilentChatter h (c.denUD C) p := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [Comp.imports_mk] at hc
  subst hc
  exact not_silentChatter_nil C h ns xs

/-- **The exporter's environment diverges only where its node does.** -/
theorem expObs_nodeDivG {p : List (Move sigU sigU)} (h : p ∈ (g.expObs (impSemD P)).div) :
    p ∈ NodeDiv 0 (Strategy.ofHandler (maskH 0)) (Node.denD (impSemD P) 0 g.expNode) := by
  rcases h with (⟨s, t, -, hs, -⟩ | hD) | ⟨I, -, L', hL', s₀, c₀, -, -, -, -, hk⟩
  · have hs' : s ∈ (DStrategy.ofHandler (maskH 0)).div := hs
    rw [DStrategy.ofHandler_div] at hs'
    exact hs'.elim
  · exact hD
  · exfalso
    obtain ⟨w', hw', -, hwL⟩ := hk 1
    have hmem := (Node.denD (impSemD P) 0 g.expNode).inf_sub hL' hwL
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hw'
    exact noInl_expNodeDG P g _ hmem x (List.mem_append_right _ (List.mem_map_of_mem hx))

/-- **A divergence of the exporter's environment** is complete rounds, then a pending question. -/
theorem expObs_div_shapeG {p : List (Move sigU sigU)} (h : p ∈ (g.expObs (impSemD P)).div) :
    ∃ (L : List (Round sigU)) (q : sigU.Op), p = twos L ++ [.inr (.ask q)] := by
  obtain ⟨x, y, hz, hx, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := expObs_nodeDivG h
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) 0 g.expNode)).div_run ⟨ha, .inr haN⟩
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, hy⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, cs, rfl⟩ := exists_rplay hy
  exact ⟨_, _, (serve_run (noInl_ofHandler_pure pure_maskH0 x hx) hz).2⟩

theorem eq_map_mk0 {E F : Sig.{0}} :
    ∀ {cl : List (CRound E F)}, (∀ r ∈ cl, r.cs = []) → cl = (cl.map CRound.toRound).map mk0
  | [], _ => rfl
  | ⟨q, cs, a⟩ :: cl, h => by
    have hcs : cs = [] := h _ List.mem_cons_self
    subst hcs
    rw [List.map_cons, List.map_cons, ← eq_map_mk0 fun r hr => h r (List.mem_cons_of_mem _ hr)]
    rfl

/-- **The exporter's environment, diverging after complete rounds, read back along one run**
(by `AdeqD`): after typed rounds `L` and a typed question `q`, a divergence of the exporter's
environment is a session of the exporter from its initial state to a state from which `q`
diverges. -/
theorem exp_div_readbackG (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) {L : List (Round sigU)}
    (hL : ∀ x ∈ L, g.exp.Typed x) {q : sigU.Op} (hq : g.exp.TypedQ q)
    (h : twos L ++ [.inr (.ask q)] ∈ (g.expObs (impSemD P)).div) :
    ∃ s, g.exp.Run P g.exp.init L s ∧ g.exp.DivStep P s q := by
  -- the node's own divergence, below `maskH 0` and `splitH 0`
  obtain ⟨x, y, hz, hx, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := expObs_nodeDivG h
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) 0 g.expNode)).div_run ⟨ha, .inr haN⟩
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, hy⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, cs, rfl⟩ := exists_rplay hy
  have hxn : NoInl x := noInl_ofHandler_pure pure_maskH0 x hx
  obtain ⟨-, hpe⟩ := serve_run hxn hz
  obtain ⟨rfl, hg₁⟩ := twos_snoc_inj hpe
  cases hg₁
  obtain ⟨low, k, H, hk, rfl⟩ := hc_zip_run (oneShot_splitH 0) ha₂ hyb hz₂
  rw [hc_splitH_inv H fun _ _ => Nat.zero_le _] at haN
  simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hk
  obtain ⟨hk, -⟩ := Prog.call.inj hk
  subst hk
  rw [halves_rplay_inr] at haN
  -- the node: the exporter's IR below `implsH 0 []`
  rw [LinkedG.expNode, div_node_inst] at haN
  rcases haN with ⟨u, v, hzN, hu, hv⟩ | hsil
  swap
  · exact absurd hsil (not_silentChatter_of_nil _ _ he.imports)
  obtain ⟨g₂, hv₂⟩ := (g.exp.comp.denUD (impSemD P)).div_run hv
  obtain ⟨up, cs₂, rfl⟩ := exists_rplay hv₂
  obtain ⟨hupn, rfl⟩ :=
    noInl_rplay (noInl_expCompG he _ ((g.exp.comp.denUD (impSemD P)).div_mem hv))
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp hu
  obtain ⟨low₂, cs', H₂, H₂', he₂⟩ := hb_zip_run (oneShot_implsH _ _) hyN hzN
  cases H₂'
  rw [hb_eq_of_nil (hb_forall₂ H₂) hupn] at he₂
  obtain ⟨hcl, hg₂, rfl⟩ := rplay_inj he₂
  subst hg₂
  have hcl' : cl = up := by
    rw [← hcl]
    exact (List.map_id' cl).symm
  subst hcl'
  -- the exporter's IR divergence law
  rw [eq_map_mk0 hupn, rplay_mk0, ← uMoves_eq] at hv
  exact (hD _ _ hL hq).1 hv

/-- **A divergence of the exporter's environment from its specification** (the converse of
`exp_div_readbackG`, by `AdeqD`): typed import calls answered by the exporter from its initial
state to `π`, renamed to the wired exports, then a typed call of export `w` on `ws` diverging
from `π`, are a divergence of the exporter's environment. -/
theorem exp_div_buildG (hD : g.exp.AdeqD P) {ds : List (Round (sigN g.imp.imports.length))}
    {π : g.exp.St} (hrun : LinkedG.ExpRun P g g.exp.init ds π) (hwt : ∀ y ∈ ds, WTG g y)
    {w : Fin g.exp.comp.exports.length} {ws : List IVal}
    (hck : ValTy.checkList g.exp.comp.exports[w].ty.params ws = true)
    (hdiv : g.exp.DivStep P π (w.val, .vals ws)) :
    twos (ds.map (wireRoundG g)) ++ [.inr (.ask (w.val, .vals ws))] ∈
      (g.expObs (impSemD P)).div := by
  have hTy : ∀ r ∈ ds.map (wireRoundG g), g.exp.Typed r := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    obtain ⟨w', ws', hwy, hp, hck'⟩ := hwt y hy
    refine ⟨w', ws', ?_, hck'⟩
    show (g.wire.getD y.1.1.val 0, y.1.2) = _
    rw [wire_getDG hwy, hp]
  have hv := (hD _ _ hTy ⟨w, ws, rfl, hck⟩).2 ⟨π, expRunG_run hrun, hdiv⟩
  rw [uMoves_eq, ← rplay_mk0] at hv
  -- the exporter's node
  have HI : HB (implsH 0 []) ((ds.map (wireRoundG g)).map (mk0 (E := sigU)))
      ((ds.map (wireRoundG g)).map mk0) :=
    HB.of_map mk0 mk0 _ fun _ _ => .cons .nil .nil
  obtain ⟨uI, huI, hzI⟩ := hb_pend HI (w.val, .vals ws) .nil
  have hN : rplay ((ds.map (wireRoundG g)).map mk0) (w.val, .vals ws) [] ∈
      (Node.denD (impSemD P) 0 g.expNode).div := by
    rw [LinkedG.expNode, div_node_inst]
    exact .inl ⟨uI, _, hzI, huI, hv⟩
  -- `splitH 0` and `maskH 0`
  have HS : HC (splitH 0) ((ds.map (wireRoundG g)).map (mk0 (E := sigU)))
      (((ds.map (wireRoundG g)).map mk0).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map (g := CRound.inr (F₁ := sigU))]
    exact HC.of_map (mk0 (E := sigU)) (CRound.inr ∘ mk0) _ fun (r : Round sigU) _ =>
      .call (h := splitH 0) (splitH_shift 0 r.1.1 r.1.2) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_pend HS (splitH_shift 0 w.val (.vals ws)) []
  have HM : HB (maskH 0) ((ds.map (wireRoundG g)).map (mk0 (E := sigU)))
      ((ds.map (wireRoundG g)).map mk0) :=
    HB.of_map mk0 mk0 _ fun _ _ => .cons .nil .nil
  obtain ⟨sM, hsM, hzM⟩ := hb_pend HM (w.val, .vals ws) .nil
  rw [← rplay_mk0]
  exact .inl (.inr ⟨sM, _, hzM, hsM, _, bS, hzS,
    ⟨rplay_pair_inr ((Node.denD (impSemD P) 0 g.expNode).div_mem hN),
      by rw [halves_rplay_inr]; exact hN⟩, hbS⟩)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
