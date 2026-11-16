module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Imp
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds
public import Silmaril.Wasm.Component.Reference.LinkedSessionFwd.Defs

/-!
# Reading back the IR plays of a linked component

`linked2_irToSpec : Linked2.IRToSpec P l` under `Linked2.Adequate l`: the typed session plays
of `l.toComp.den (impSem P)` (`Linked2.sessMoves`) are read back into a `Linked2.SessSpec`
session from the instances' stores. The layers, from the top:

* `atSizes` and the linked export handler (`den_env`): the export questions `(j, .vals vs)` of
  the linked component, as questions `n_A + j` of its environment `envL`;
* the composition of the importer's node over the exporter's environment (`serve_inv`): rounds
  `cl` of the importer's side whose lower calls, all together and in order, are complete
  rounds of the exporter's environment;
* `splitH`, the pairing and the importer's node (`hc_splitH_inv`, `cplay_of_pair_inr`,
  `hb_inv`): rounds of the importer's IR `l.imp.toComp.denU`, its import calls forwarded to the
  wired exports (`hrounds_wire_inv`);
* the importer's IR (`imp_readback`): rounds of its core instance from its store, the import
  calls related by `ImpRel`;
* the exporter (`expEnv_specRoundsT`): `specRoundsT_of_den` through the exporter's node, read as
  a session of the exporter (`sessRounds_of_specRoundsT`) and, the calls being typed and wired,
  as an `ExpRunT` (`expRunT_of_sessRounds`);
* the session (`sessSpec_of`): the instance's play and the `ExpRunT` split round by round.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The top: `atSizes` and the linked export handler -/

/-- A linked call as a question of the linked environment, with its answer. -/
def topR (l : Linked2) (co : (Fin l.imp.exports.length × List IVal) × Option (List IVal)) :
    Round sigU :=
  ⟨(l.exp.exports.length + co.1.1.val, .vals co.1.2), co.2.map .vals⟩

/-- The rounds of a session play. -/
def topRounds (l : Linked2) :
    List (Fin l.imp.exports.length × List IVal) → List (Option (List IVal)) →
    List (Round (sigN l.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    ⟨(⟨j, by simp [Linked2.exports_length_toComp]⟩, .vals vs), o.map .vals⟩ :: topRounds l cs os
  | _, _ => []

theorem sessMoves_eq (l : Linked2) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      Linked2.sessMoves l calls outs = twos (topRounds l calls outs)
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: _ :: Linked2.sessMoves l cs os = _ :: _ :: twos (topRounds l cs os)
    rw [sessMoves_eq l cs os]

theorem hrounds_exportsL_inv (l : Linked2) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (low : List (Round sigU)), calls.length = outs.length →
      HRounds (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
        ((topRounds l calls outs).map Round.forget) low →
      low = (calls.zip outs).map (topR l)
  | [], _, low, _, H => by cases H; rfl
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | (j, vs) :: cs, o :: os, low, hlen, H => by
    have H' : HRounds (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
        (⟨(j.val, .vals vs), o.map .vals⟩ :: (topRounds l cs os).map Round.forget) low := H
    rcases hrounds_cons_inv H' with ⟨hq, -⟩ | ⟨q', k, a', low', rfl, hq, hk, H''⟩
    · rw [exportsH_toCompL l j.isLt] at hq
      cases hq
    · rw [exportsH_toCompL l j.isLt] at hq
      cases hq
      cases hk
      rw [hrounds_exportsL_inv l cs os low' (by simpa using hlen) H'']
      rfl

/-- **The top layers**: a session play of the linked component is a play of complete rounds
of its environment. -/
theorem den_env {P : Profile} {l : Linked2} {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (hlen : calls.length = outs.length)
    (h : twos (topRounds l calls outs) ∈ l.toComp.den (impSem P)) :
    twos ((calls.zip outs).map (topR l)) ∈ envL (impSem P) l := by
  unfold Comp.den atSizes at h
  obtain ⟨l₁, Hn, hl⟩ := hrounds_of_comp (oneShot_narrowH _) (fun s _ => noInl_sigN_nil rfl s) h
  rw [hrounds_narrowH_inv _ Hn] at hl
  have hEnv : ∀ t ∈ envL (impSem P) l, NoInl t :=
    noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  have hU : ∀ t ∈ l.toComp.denU (impSem P), NoInl t := by
    rw [denU_toCompL]
    exact noInl_comp hEnv
  have hl₁ := twos_of_comp_noInl hU hl
  rw [denU_toCompL] at hl₁
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv hl₁
  rw [hrounds_exportsL_inv l calls outs l₂ hlen H₂] at hl₂
  exact hl₂

/-! ## The exporter -/

/-- `specRoundsT_of_den` at the untyped interface. -/
theorem specRoundsT_of_denU {P : Profile} {c : Simple} {I : SInst} (hc : c.Good)
    (hI : c.mod.IsInst I) {L : List (Round sigU)} (hl₁ : twos L ∈ c.toComp.denU (modSem P)) :
    SpecRoundsT P c I I.store L := by
  have hN : ∀ t ∈ coreNode (modSem P) 0 c.mod [], NoInl t :=
    noInl_comp (noInl_ofHandler_pure (pure_implsN_nil 0 _))
  have hX : ∀ t ∈ ((Strategy.id sigU).pair (coreNode (modSem P) 0 c.mod [])).comp
      (Strategy.ofHandler (splitH 0)), NoInl t :=
    noInl_pair_comp (oneShot_splitH 0) (fun q f k hq => by
      simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hq
      cases hq
      exact ⟨_, rfl⟩) hN
  have hEnv : ∀ t ∈ envS (modSem P) c, NoInl t :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  rw [denU_toComp] at hl₁
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv hl₁
  have hl₃ := twos_of_comp_noInl hX hl₂
  have hpair : ∀ s ∈ (Strategy.id sigU).pair (coreNode (modSem P) 0 c.mod []),
      ∀ t ∈ Strategy.ofHandler (splitH 0), ∀ {p : List (Move sigU sigU)}, Zip s t p → NoInl s := by
    intro s hs t ht p hz
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
    refine noInl_of_pair hN hs fun q hm => ?_
    obtain ⟨q', k, hk⟩ := run_ask_mem (oneShot_splitH 0) t .idle y
      (show RunInv (splitH 0) .idle from trivial) hy _ (zip_inr_left_mem hz hm)
    simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hk
    cases hk
  obtain ⟨l₃, H₃, hl₃'⟩ := hrounds_of_comp_of (oneShot_splitH 0) hpair hl₃
  rw [hrounds_splitH0_inv H₃] at hl₃'
  have hl₄ := twos_of_pair_inr hl₃'
  have hY : ∀ t ∈ ((modSem P).sem c.mod).comp
      (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)), NoInl t :=
    noInl_comp (fun s _ => noInl_sigN0 s)
  have hl₅ := twos_of_comp_noInl hY hl₄
  obtain ⟨l₄, H₄, hl₆⟩ := hrounds_of_comp (oneShot_widenH _) (fun s _ => noInl_sigN0 s) hl₅
  rw [modSem_sem hI] at hl₆
  have hZ : ∀ t ∈ (I.strategy P I.store).comp (Strategy.ofHandler (exportH (instNum hI))),
      NoInl t := noInl_comp (fun s _ => noInl_inst hI.2.1 s)
  have hl₇ := twos_of_comp_noInl hZ hl₆
  obtain ⟨l₅, H₅, hl₈⟩ := hrounds_of_comp (oneShot_exportH _) (fun s _ => noInl_inst hI.2.1 s) hl₇
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp hl₈
  obtain ⟨s', hA⟩ := acts_of_path l₅ hq
  exact specRoundsT_of_chain hc hI _ l₂ l₄ l₅ I.store s' H₂ H₄ H₅ hA

/-- **The exporter's environment read back**: complete rounds of the first environment of the
linked component are specification rounds of the exporter from its instance's store. -/
theorem expEnv_specRoundsT {P : Profile} {l : Linked2} {I : SInst} (he : l.exp.Good)
    (hI : l.exp.mod.IsInst I) {L : List (Round sigU)}
    (h : twos L ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l)) :
    SpecRoundsT P l.exp I I.store L := by
  have hD : ∀ t ∈ l.exp.toComp.denU (modSem P), NoInl t := by
    rw [denU_toComp]
    exact noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  have hN : ∀ t ∈ expNode (impSem P) l, NoInl t :=
    noInl_comp (noInl_ofHandler_pure fun _ => ⟨none, rfl⟩)
  have hX : ∀ t ∈ ((Strategy.id sigU).pair (expNode (impSem P) l)).comp
      (Strategy.ofHandler (splitH 0)), NoInl t :=
    noInl_pair_comp (oneShot_splitH 0) (fun q f k hq => by
      simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hq
      cases hq
      exact ⟨_, rfl⟩) hN
  unfold ext at h
  have hl₃ := twos_of_comp_noInl hX h
  have hpair : ∀ s ∈ (Strategy.id sigU).pair (expNode (impSem P) l),
      ∀ t ∈ Strategy.ofHandler (splitH 0), ∀ {p : List (Move sigU sigU)}, Zip s t p → NoInl s := by
    intro s hs t ht p hz
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp ht
    refine noInl_of_pair hN hs fun q hm => ?_
    obtain ⟨q', k, hk⟩ := run_ask_mem (oneShot_splitH 0) t .idle y
      (show RunInv (splitH 0) .idle from trivial) hy _ (zip_inr_left_mem hz hm)
    simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hk
    cases hk
  obtain ⟨l₃, H₃, hl₃'⟩ := hrounds_of_comp_of (oneShot_splitH 0) hpair hl₃
  rw [hrounds_splitH0_inv H₃] at hl₃'
  have hl₄ := twos_of_pair_inr hl₃'
  have hU : ∀ t ∈ (SimpleI.ofSimple l.exp).toComp.denU (impSem P), NoInl t := by
    rw [denU_ofSimple]
    exact hD
  have hl₅ := twos_of_comp_noInl hU hl₄
  rw [denU_ofSimple] at hl₅
  exact specRoundsT_of_denU he hI hl₅

/-! ## The wiring -/

theorem wired {l : Linked2} (hw : l.WireTy) {k : Nat} (hk : k < l.imp.imports.length) :
    ∃ w : Fin l.exp.exports.length, l.wire[k]? = some w.val ∧
      (l.imp.imports[k]?).map (fun p : String × FuncTy => p.2) = some l.exp.exports[w].ty := by
  have hk' : k < l.wire.length := by
    rw [hw.length]
    exact hk
  obtain ⟨x, hx, hty⟩ := hw.ty k l.wire[k] (List.getElem?_eq_getElem hk')
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hx
  exact ⟨⟨_, hlt⟩, List.getElem?_eq_getElem hk',
    hty.trans (congrArg (fun y : SimpleExport => some y.ty) hget.symm)⟩

/-- A component import call wired to an export of the exporter, on values of its type. -/
def WT (l : Linked2) (y : Round (sigN l.imp.imports.length)) : Prop :=
  ∃ (w : Fin l.exp.exports.length) (ws : List IVal), l.wire[y.1.1.val]? = some w.val ∧
    y.1.2 = .vals ws ∧ ValTy.checkList l.exp.exports[w].ty.params ws = true

theorem wt_of {l : Linked2} (hw : l.WireTy) {y : Round (sigN l.imp.imports.length)}
    {nm : String} {ft : FuncTy} {ws : List IVal}
    (hft : l.imp.imports[y.1.1.val]? = some (nm, ft)) (hy : y.1.2 = .vals ws)
    (hck : ValTy.checkList ft.params ws = true) : WT l y := by
  obtain ⟨w, hwk, hty⟩ := wired hw y.1.1.isLt
  rw [hft] at hty
  have hft' : ft = l.exp.exports[w].ty := by simpa using hty
  exact ⟨w, ws, hwk, hy, hft' ▸ hck⟩

theorem impRel_typed {c : SimpleI} {I : SInst} {x : Σ e : I.E.Op, I.E.Ar e}
    {ds : List (Round (sigN c.imports.length))} (h : ImpRel c I x ds) :
    ∀ y ∈ ds, ∃ (nm : String) (ft : FuncTy) (ws : List IVal),
      c.imports[y.1.1.val]? = some (nm, ft) ∧ y.1.2 = .vals ws ∧
        ValTy.checkList ft.params ws = true := by
  obtain ⟨nm, ft, A, hft, -, hm⟩ := h
  split at hm
  · obtain ⟨-, rfl⟩ := hm
    intro y hy
    cases hy
  · rename_i ws hl
    obtain ⟨hk, R, rfl, -⟩ := hm
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact ⟨nm, ft, ws, hft, rfl, checkList_of_liftArgs hl⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ y ∈ b, ∃ x, R x y
  | _, _, .nil, _, hy => nomatch hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, h⟩
    · exact forall₂_mem_right t y hy

/-- The importer's node forwards each wired import call to the wired export
(`hrounds_wire` in reverse). -/
theorem hrounds_wire_inv {l : Linked2} (hw : l.WireTy) :
    ∀ (ds : List (Round (sigN l.imp.imports.length))) (cs' : List (Round sigU)),
      HRounds (implsH l.exp.exports.length (wireArgs l)) (ds.map Round.forget) cs' →
      cs' = ds.map (wireRound l)
  | [], _, H => by cases H; rfl
  | ⟨(k, p), R⟩ :: ds, cs', H => by
    obtain ⟨w, hwk, -⟩ := wired hw k.isLt
    have H' : HRounds (implsH l.exp.exports.length (wireArgs l))
        (⟨(k.val, p), R⟩ :: ds.map Round.forget) cs' := H
    rcases hrounds_cons_inv H' with ⟨hq, -⟩ | ⟨q', k', a', low', rfl, hq, hk, H''⟩
    · rw [implsH_wire hwk] at hq
      cases hq
    · rw [implsH_wire hwk] at hq
      cases hq
      cases hk
      rw [hrounds_wire_inv hw ds low' H'']
      simp only [List.map_cons, wireRound, wire_getD hwk]

/-! ## The exporter's calls -/

/-- **A session of the exporter on typed wired calls is an `ExpRunT`.** -/
theorem expRunT_of_sessRounds {P : Profile} {l : Linked2} {I : SInst} :
    ∀ {s s' : Store Nat} (ds : List (Round (sigN l.imp.imports.length))), (∀ d ∈ ds, WT l d) →
      SessRounds P l.exp I s (ds.map (wireRound l)) s' → Linked2.ExpRunT P l I s ds s'
  | s, _, [], _, h => by
    cases h
    exact .nil s
  | _, _, ⟨(k, p), R⟩ :: ds, hwt, h => by
    obtain ⟨w, ws, hw, hp, hck⟩ := hwt _ List.mem_cons_self
    have hp' : p = .vals ws := hp
    subst hp'
    have e : wireRound l ⟨(k, .vals ws), R⟩ = ⟨(w.val, .vals ws), R⟩ := by
      simp only [wireRound, wire_getD hw]
    rw [List.map_cons, e] at h
    have hwt' : ∀ d ∈ ds, WT l d := fun d hd => hwt d (List.mem_cons_of_mem _ hd)
    cases h with
    | bad _ hn _ =>
      exact absurd (hn w.isLt ws rfl) (by rw [Bool.not_eq_false]; exact hck)
    | ret _ hret h' => exact .ret w hw hret (expRunT_of_sessRounds ds hwt' h')
    | trap _ htrap h' => exact .trap w hw htrap (expRunT_of_sessRounds ds hwt' h')

theorem expRunT_split {P : Profile} {l : Linked2} {I : SInst} :
    ∀ {s s' : Store Nat} (ds ds' : List (Round (sigN l.imp.imports.length))),
      Linked2.ExpRunT P l I s (ds ++ ds') s' →
      ∃ s₁, Linked2.ExpRunT P l I s ds s₁ ∧ Linked2.ExpRunT P l I s₁ ds' s'
  | s, _, [], _, h => ⟨s, .nil s, h⟩
  | _, _, _ :: ds, ds', h => by
    rw [List.cons_append] at h
    cases h with
    | ret w hw hret h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunT_split ds ds' h'
      exact ⟨s₁, .ret w hw hret h₁, h₂⟩
    | trap w hw htrap h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunT_split ds ds' h'
      exact ⟨s₁, .trap w hw htrap h₁, h₂⟩

/-! ## The rounds of the session -/

theorem round_of {l : Linked2} (hw : l.WireTy) {Ii : SInst} {r : CRound Ii.E Ii.F}
    {c : CRound sigU sigU} {co : (Fin l.imp.exports.length × List IVal) × Option (List IVal)}
    (h : ∃ x, RdI l.imp Ii r x ∧
      HBR (implsH l.exp.exports.length (wireArgs l)) x (downBy l.exp.exports.length c))
    (hc : CRound.toRound c = topR l co) :
    ∃ d : Linked2.SessRound l Ii, d.Ok ∧ LinkedSessionIR.SessRound.r d = r ∧
      c.cs = d.dss.flatten.map (wireRound l) ∧ ((d.j, d.vs) = co.1 ∧ d.ans = co.2.map .vals) ∧
      ∀ y ∈ d.dss.flatten, WT l y := by
  obtain ⟨cq, ccs, ca⟩ := c
  obtain ⟨⟨j₀, vs₀⟩, o⟩ := co
  obtain ⟨rq, rcs, ra⟩ := r
  have hcq : cq = (l.exp.exports.length + j₀.val, .vals vs₀) := congrArg Sigma.fst hc
  subst hcq
  have hca : ca = o.map .vals := eq_of_heq (Sigma.mk.inj hc).2
  subst hca
  obtain ⟨x, hRd, q, a, cs, cs', rfl, hy, H⟩ := h
  cases hy
  obtain ⟨j, vs, xs, dss, hxq, hcl, h₁, h₂, hF, hxcs, hxa⟩ := hRd
  have hxq' : ((l.exp.exports.length + j₀.val - l.exp.exports.length, Payload.vals vs₀) :
      Nat × Payload) = (j.val, .vals vs) := hxq
  rw [Nat.add_sub_cancel_left] at hxq'
  simp only [Prod.mk.injEq, Payload.vals.injEq] at hxq'
  obtain ⟨hj, rfl⟩ := hxq'
  have hj' : j₀ = j := Fin.ext hj
  subst hj'
  have hxcs' : cs = dss.flatten.map Round.forget := hxcs
  subst hxcs'
  have hcs := hrounds_wire_inv hw dss.flatten ccs H
  refine ⟨⟨j₀, vs₀, rq, rcs, ra, dss⟩, ⟨xs, hcl, h₁, h₂, hF⟩, rfl, hcs, ⟨rfl, hxa.symm⟩, ?_⟩
  intro y hy
  obtain ⟨ds, hds, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨x', hx'⟩ := forall₂_mem_right hF ds hds
  obtain ⟨nm, ft, ws, hft, hp, hck⟩ := impRel_typed hx' y hy
  exact wt_of hw hft hp hck

theorem build_rounds {l : Linked2} (hw : l.WireTy) {Ii : SInst} :
    ∀ {ri : List (CRound Ii.E Ii.F)} {cl : List (CRound sigU sigU)}
      {cos : List ((Fin l.imp.exports.length × List IVal) × Option (List IVal))},
      List.Forall₂ (fun r c => ∃ x, RdI l.imp Ii r x ∧
        HBR (implsH l.exp.exports.length (wireArgs l)) x (downBy l.exp.exports.length c)) ri cl →
      List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl cos →
      ∃ ds : List (Linked2.SessRound l Ii), (∀ d ∈ ds, d.Ok) ∧
        ds.map LinkedSessionIR.SessRound.r = ri ∧
        cl.flatMap (·.cs) = (ds.flatMap fun d => d.dss.flatten).map (wireRound l) ∧
        List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.map .vals) ds cos ∧
        ∀ y ∈ ds.flatMap (fun d => d.dss.flatten), WT l y
  | _, _, _, .nil, .nil => ⟨[], fun _ h => (nomatch h), rfl, rfl, .nil, fun _ h => (nomatch h)⟩
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    obtain ⟨d, hOk, hr, hcs, hjo, hwt⟩ := round_of hw h₁ h₂
    obtain ⟨ds, hOks, hrs, hcss, hF, hwts⟩ := build_rounds hw t₁ t₂
    refine ⟨d :: ds, ?_, by rw [List.map_cons, hr, hrs], ?_, .cons hjo hF, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact hOk
      · exact hOks d' hd'
    · rw [List.flatMap_cons, List.flatMap_cons, hcs, hcss, List.map_append]
    · intro y hy
      rw [List.flatMap_cons, List.mem_append] at hy
      rcases hy with hy | hy
      · exact hwt y hy
      · exact hwts y hy

/-! ## The session -/

theorem path_split_inst {I : SInst} {P : Profile} :
    ∀ {q q'' : I.HState} {c c' : List (Move I.E I.F)}, I.Path P q (c ++ c') q'' →
      ∃ q', I.Path P q c q' ∧ I.Path P q' c' q''
  | _, _, [], _, h => ⟨_, .nil _, h⟩
  | _, _, _ :: c, c', h => by
    rw [List.cons_append] at h
    cases h with
    | cons t h =>
      obtain ⟨q', h₁, h₂⟩ := path_split_inst (c := c) h
      exact ⟨q', .cons t h₁, h₂⟩

theorem path_ans_idle {I : SInst} {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    {f : I.F.Op} {w : I.F.Ar f} (h : I.Path P q (p ++ [.inr (.ans f w)]) q') :
    ∃ s, q' = .idle s := by
  obtain ⟨q₁, -, h₂⟩ := path_split_inst h
  cases h₂ with
  | cons t h₃ =>
    cases t with
    | oret _ _ _ =>
      cases h₃
      exact ⟨_, rfl⟩

/-- **Rounds of the importer and an `ExpRunT` are a specification session.** -/
theorem sessSpec_of {P : Profile} {l : Linked2} {Ie Ii : SInst} :
    ∀ (ds : List (Linked2.SessRound l Ii)) (calls : List (Fin l.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) {u π π' : Store Nat} {q : Ii.HState},
      List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.map .vals) ds
        (calls.zip outs) →
      calls.length = outs.length → (∀ d ∈ ds, d.Ok) →
      Ii.Path P (.idle u) (ds.flatMap Linked2.SessRound.instMoves) q →
      Linked2.ExpRunT P l Ie π (ds.flatMap fun d => d.dss.flatten) π' →
      ∃ u', Linked2.SessSpec P l Ie Ii u π calls outs u' π'
  | [], calls, outs, u, π, π', q, hF, hlen, _, _, hrun => by
    cases hrun
    have hz : calls.zip outs = [] := List.forall₂_nil_left_iff.mp hF
    rcases List.zip_eq_nil_iff.mp hz with rfl | rfl
    · have : outs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst this
      exact ⟨u, .nil u π⟩
    · have : calls = [] := List.length_eq_zero_iff.mp hlen
      subst this
      exact ⟨u, .nil u π⟩
  | d :: ds, calls, outs, u, π, π', q, hF, hlen, hOk, hp, hrun => by
    rcases calls with _ | ⟨c, cs⟩
    · cases hF
    rcases outs with _ | ⟨o, os⟩
    · cases hF
    have hF' : List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.map .vals)
        (d :: ds) ((c, o) :: cs.zip os) := hF
    obtain ⟨⟨hdc, hans⟩, hF''⟩ := List.forall₂_cons.mp hF'
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunT_split _ _ hrun
    obtain ⟨u', hS⟩ := sessSpec_of ds cs os hF'' (by simpa using hlen)
      (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂
    subst hdc
    exact ⟨u', .round d (hOk d List.mem_cons_self) hp₁ hr₁ hans hS⟩

/-! ## The theorem -/

/-- **The IR to specification direction of linked sessions** (proved under
`Linked2.Adequate`). -/
theorem linked2_irToSpec (P : Profile) (l : Linked2) (hl : l.Adequate) :
    Linked2.IRToSpec P l := by
  intro Ie Ii hIe hIi calls outs ht hlen h
  rw [sessMoves_eq] at h
  have hE := den_env hlen h
  have hσ : ∀ s ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l), NoInl s :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  obtain ⟨cl, hcl, hA, hmap⟩ := serve_inv hσ hE
  have K : List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl (calls.zip outs) :=
    forall₂_of_map_eq hmap
  obtain ⟨low₁, H₁, hlow₁⟩ := hc_inv (oneShot_splitH _) hcl
  have hge : ∀ r ∈ cl, l.exp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨co, hco⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (l.exp.exports.length + co.1.1.val, .vals co.1.2) := congrArg Sigma.fst hco
    rw [h₁]
    exact Nat.le_add_right _ _
  rw [hc_splitH_inv H₁ hge] at hlow₁
  have hN := cplay_of_pair_inr hlow₁
  obtain ⟨up₂, H₂, hup₂⟩ := hb_inv (oneShot_implsH _ _) hN
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
  obtain ⟨ri, hri, F⟩ := imp_readback hl.impGood hIi htop hup₂
  obtain ⟨ds, hOk, hr, hcs, hF, hWT⟩ := build_rounds hl.wireTy (forall₂_comp F G₂) K
  rw [hcs] at hA
  have hspec := expEnv_specRoundsT hl.expGood hIe hA
  obtain ⟨s', hS⟩ := sessRounds_of_specRoundsT hspec fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w, ws, hw, -, -⟩ := hWT y hy
    show (l.wire.getD y.1.1.val 0) < _
    rw [wire_getD hw]
    exact w.isLt
  have hrun := expRunT_of_sessRounds _ hWT hS
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp hri
  rw [← hr, LinkedSessionIR.cplay_r] at hq
  obtain ⟨u', hS'⟩ := sessSpec_of ds calls outs hF hlen hOk hq hrun
  exact ⟨u', s', hS'⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
