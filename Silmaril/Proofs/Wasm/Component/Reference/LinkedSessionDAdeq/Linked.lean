module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Imp
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked
public import Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Defs

/-!
# Reading back the divergences of a linked component from the importer's node

* `lowAsk_denUD`: the lower questions of a component go through its import mask, so they are in
  range; `not_silentChatter_impNode`, `div_impNode`: the importer's node of a `Linked2` forwards
  every import call in range to the exporter (`implsH` on `⟨[], .call w⟩`, under `WireTy`), so it
  has no silent chatter: it diverges exactly where the nested importer does;
* `top_div`: the outer handlers (`narrowH`, `widenH 0`, the linked export handler) on a pending
  session play: the environment's play is the session's rounds, then the pending question;
* `sessDivsB_of_nodeDiv`: an IR divergence from the importer's node after a typed session is a
  specification session followed by a round of the importer diverging host-free: the exporter's
  environment served all the import calls (`serve_run`), the importer's node forwards them
  (`hb_zip_run`, `hrounds_wire_inv`), the importer's IR is read back by `imp_div_readback`, the
  exporter's rounds by `expEnv_specRoundsT`.
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

/-! ## Lower questions of a component -/

theorem maskH_call {n : Nat} {q m : Nat × Payload} {k : Option Payload → Prog sigU (Option Payload)}
    (h : maskH n q = .call m k) : m.1 < n := by
  simp only [maskH, Target.prog] at h
  split at h
  · obtain ⟨rfl, -⟩ := Prog.call.inj h
    assumption
  · cases h

theorem lowAsk_denNodesD {M : Type} [CoreModule M] (C : DCoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU) {s : List (Move X sigU)} {a : Ev X},
      s ∈ (denNodesD C e ns D).toStrategy → Sum.inl a ∈ s → ∃ s' ∈ D.toStrategy, Sum.inl a ∈ s'
  | _, [], _, s, _, hs, ha => by
    rw [denNodesD] at hs
    exact ⟨s, hs, ha⟩
  | e, n :: ns, D, _, _, hs, ha => by
    rw [denNodesD] at hs
    obtain ⟨s', hs', ha'⟩ := lowAsk_denNodesD C _ ns _ hs ha
    obtain ⟨s₁, hs₁, t₁, -, hz⟩ := hs'
    exact ⟨s₁, hs₁, zip_inl_mem hz ha'⟩

/-- **The lower questions of a component are in range**: they go through its import mask. -/
theorem lowAsk_denUD {M : Type} [CoreModule M] (C : DCoreSem M) (I : Iface) (ns : List (Node M))
    (xs : List Export) {s : List (Move sigU sigU)} {m : sigU.Op}
    (hs : s ∈ ((Comp.mk I ns xs).denUD C).toStrategy) (hm : Sum.inl (Ev.ask m) ∈ s) :
    m.1 < I.length := by
  rw [Comp.denUD] at hs
  obtain ⟨s₁, hs₁, t₁, -, hz⟩ := hs
  obtain ⟨s₂, hs₂, hm₂⟩ := lowAsk_denNodesD C _ ns _ hs₁ (zip_inl_mem hz hm)
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp hs₂
  obtain ⟨q, k, hk⟩ := run_ask_mem (oneShot_maskH _) s₂ .idle y trivial hy m hm₂
  exact maskH_call hk

/-! ## The importer's node -/

theorem expNode_width (l : Linked2) : l.expNode.width = l.exp.exports.length :=
  exports_length_ofSimple l.exp

/-- **No silent chatter at the importer's node**: its wiring forwards every import call in
range to the exporter, and the nested importer only calls in range. -/
theorem not_silentChatter_impNode (C : DCoreSem ImpModule) {l : Linked2} (hw : l.WireTy)
    {p : List (Move sigU sigU)} :
    ¬ SilentChatter (implsH l.expNode.width (wireArgs l)) (l.imp.toComp.denUD C) p := by
  rintro ⟨I, hI, t₀, ht₀, ⟨g, hg⟩, hsil, -⟩
  have hinf := (l.imp.toComp.denUD C).inf_isInf hI
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
    have hmem := (l.imp.toComp.denUD C).inf_sub hI hx
    obtain ⟨z, hz⟩ := (l.imp.toComp.denUD C).toStrategy.legal hmem
    rw [List.append_nil] at hz
    obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hz
    obtain rfl := Path.det hg hy
    cases hst with
    | call _ m =>
      obtain ⟨r₀, hr₀⟩ := he
      have hlt : m.1 < l.imp.imports.length :=
        lowAsk_denUD C _ _ _ hmem (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨w, hwk, -⟩ := wired hw hlt
      have e := (implsH_wire hwk m.2).symm.trans
        ((congrArg (fun n => implsH n (wireArgs l) (m.1, m.2)) (expNode_width l)).symm.trans hr₀)
      cases e

/-- **The divergences of the importer's node** (under `WireTy`): those of the nested importer
through its wiring. -/
theorem div_impNode (C : DCoreSem ImpModule) {l : Linked2} (hw : l.WireTy) :
    (Node.denD C l.expNode.width l.impNode).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsH l.expNode.width (wireArgs l)) ∧
        v ∈ (l.imp.toComp.denUD C).div} := by
  rw [Linked2.impNode, div_node_inst]
  ext p
  exact or_iff_left (not_silentChatter_impNode C hw)

/-! ## Rounds without lower calls -/

section Mk0

variable {E F G : Sig.{0}}

/-- A round without lower calls. -/
def mk0 (r : Round F) : CRound E F := ⟨r.1, [], r.2⟩

theorem cplay_mk0 : ∀ L : List (Round F), cplay (E := E) (L.map mk0) = twos L
  | [] => rfl
  | ⟨q, a⟩ :: L =>
    congrArg (fun x => Sum.inr (Ev.ask q) :: Sum.inr (Ev.ans q a) :: x) (cplay_mk0 L)

theorem rplay_mk0 (L : List (Round F)) (g : F.Op) :
    rplay (E := E) (L.map mk0) g [] = twos L ++ [.inr (.ask g)] := by
  rw [rplay, cplay_mk0]
  rfl

theorem toRound_mk0 (L : List (Round F)) : (L.map (mk0 (E := E))).map CRound.toRound = L := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    obtain ⟨q, a⟩ := r
    rw [List.map_cons, List.map_cons, ih]
    rfl

theorem hc_mk0 {h : Handler F G} :
    ∀ {L : List (Round G)} {low : List (CRound E F)},
      HC h (L.map mk0) low → ∃ l : List (Round F), low = l.map mk0 ∧ HRounds h L l
  | [], low, H => by
    cases H
    exact ⟨[], rfl, .nil⟩
  | ⟨q, a⟩ :: L, low, H => by
    change HC h (⟨q, [], a⟩ :: L.map mk0) low at H
    cases H with
    | pure hq H' =>
      obtain ⟨l, rfl, H''⟩ := hc_mk0 H'
      exact ⟨l, rfl, .pure hq H''⟩
    | call hq hk H' =>
      obtain ⟨l, rfl, H''⟩ := hc_mk0 H'
      exact ⟨⟨_, _⟩ :: l, rfl, .call hq hk H''⟩

theorem hb_mk0 {h : Handler E F} :
    ∀ {L : List (Round G)} {low : List (CRound E G)}, HB h (L.map (mk0 (E := F))) low →
      low = L.map mk0
  | [], low, H => by
    cases H
    rfl
  | ⟨q, a⟩ :: L, low, H => by
    change HB h (⟨q, [], a⟩ :: L.map mk0) low at H
    cases H with
    | cons Hc H' =>
      cases Hc
      rw [hb_mk0 H']
      rfl

theorem map_mk0_inj {l l' : List (Round F)} (h : l.map (mk0 (E := E)) = l'.map mk0) : l = l' := by
  have := congrArg (List.map CRound.toRound) h
  rwa [toRound_mk0, toRound_mk0] at this

/-- `hc_zip_run` on plays without lower calls. -/
theorem hrounds_zip_run {h : Handler F G} (hh : OneShot h) {L : List (Round G)} {g : G.Op}
    {l : List (Round F)} {f : F.Op} {t : List (Move F G)} {y : h.toReduction.toLTS.State}
    (ht : h.toReduction.toLTS.Run .idle t y)
    (hz : Zip (twos l ++ [.inr (.ask f)] : List (Move E F)) t (twos L ++ [.inr (.ask g)])) :
    HRounds h L l ∧ ∃ k : F.Ar f → G.Ar g, h g = .call f fun r => .pure (k r) := by
  rw [← rplay_mk0, ← rplay_mk0] at hz
  obtain ⟨low, k, H, hk, he⟩ := hc_zip_run hh (path_rplay _ _ _) ht hz
  obtain ⟨rfl, -, -⟩ := rplay_inj he
  obtain ⟨l', he', H'⟩ := hc_mk0 H
  obtain rfl := map_mk0_inj he'
  exact ⟨H', k, hk⟩

/-- `hb_zip_run` on plays without lower calls. -/
theorem hb_zip_twos {h : Handler E F} (hh : OneShot h) {L : List (Round G)} {g : G.Op}
    {s : List (Move E F)} {y : h.toReduction.toLTS.State} {p : List (Move E G)}
    (hr : h.toReduction.toLTS.Run .idle s y)
    (hz : Zip s (twos L ++ [.inr (.ask g)] : List (Move F G)) p) :
    p = twos L ++ [.inr (.ask g)] := by
  rw [← rplay_mk0] at hz
  obtain ⟨low, cs', H, H', rfl⟩ := hb_zip_run hh hr hz
  cases H'
  rw [hb_mk0 H, rplay_mk0]

end Mk0

/-! ## The outer handlers -/

theorem envAfter_link (l : Linked2) :
    envAfter 0 [l.expNode, l.impNode] = l.exp.exports.length + l.imp.exports.length := by
  simp [envAfter, Node.width, Linked2.expNode, Linked2.impNode, SimpleI.ofSimple,
    SimpleI.exports_length_toComp]

theorem noInl_twos_ask {E F : Sig.{0}} {L : List (Round F)} {g : F.Op} :
    NoInl (twos L ++ [.inr (.ask g)] : List (Move E F)) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact noInl_twos L e he
  · simp at he

/-- **The outer handlers on a pending session play**: below `narrowH`, `widenH 0` and the
linked export handler, the environment's pending play is the session's rounds, then the call of
the importer's export `j` on `vs` (environment function `exp.exports.length + j`). -/
theorem top_div {l : Linked2} {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    {s : List (Move (sigN 0) sigU)} {t : List (Move sigU (sigN l.compExports.length))}
    {u : List (Move (sigN 0) sigU)} {v d x : List (Move sigU sigU)} {Ld : List (Round sigU)}
    {gd : sigU.Op} (h₁ : Zip u v s)
    (h₂ : Zip s t (Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))]))
    (hu : u ∈ Strategy.ofHandler (widenH 0))
    (ht : t ∈ Strategy.ofHandler (narrowH l.compExports.length)) (h₃ : Zip d x v)
    (hd : d = twos Ld ++ [.inr (.ask gd)])
    (hx : x ∈ Strategy.ofHandler (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports)) :
    Ld = (calls.zip outs).map (topR l) ∧ gd = (l.exp.exports.length + j.val, .vals vs) := by
  subst hd
  rw [envAfter_link] at hx
  obtain ⟨yx, hyx⟩ := Strategy.mem_ofHandler.mp hx
  have hdrun : Path .idle (twos Ld ++ [.inr (.ask gd)] : List (Move sigU sigU)) (.run gd) :=
    (path_twos Ld).append (.single (.ask gd))
  obtain ⟨gv, hv⟩ := run_of_zip_top h₃ hdrun hyx
  have hvn : NoInl v := fun e he => noInl_twos_ask e (zip_inl_mem h₃ he)
  rcases shape_of_noInl v hv hvn with ⟨h, -⟩ | ⟨q, Lv, hq, rfl⟩
  · cases h
  cases hq
  obtain ⟨yu, hyu⟩ := Strategy.mem_ofHandler.mp hu
  have hs := hb_zip_twos (oneShot_widenH 0) hyu h₁
  subst hs
  rw [sessMoves_eq] at h₂
  obtain ⟨yt, hyt⟩ := Strategy.mem_ofHandler.mp ht
  obtain ⟨H₁, k₁, hk₁⟩ := hrounds_zip_run (oneShot_narrowH _) hyt h₂
  have hLv := hrounds_narrowH_inv _ H₁
  obtain ⟨hq₁, -⟩ := Prog.call.inj hk₁
  subst hq₁ hLv
  obtain ⟨H₂, k₂, hk₂⟩ := hrounds_zip_run (oneShot_implsH _ _) hyx h₃
  refine ⟨hrounds_exportsL_inv l calls outs Ld hlen H₂, ?_⟩
  have e := (exportsH_toCompL l j.isLt (.vals vs)).symm.trans hk₂
  exact (Prog.call.inj e).1.symm

/-! ## The sources -/

theorem irDiv_union (C : DCoreSem ImpModule) (l : Linked2) (S T : Set (List (Move sigU sigU))) :
    l.irDiv C (S ∪ T) = l.irDiv C S ∪ l.irDiv C T := by
  ext p
  constructor
  · rintro ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, hd | hd, hx⟩
    · exact .inl ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, hd, hx⟩
    · exact .inr ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, hd, hx⟩
  · rintro (⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, hd, hx⟩ |
      ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, hd, hx⟩)
    · exact ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, .inl hd, hx⟩
    · exact ⟨s, t, u, v, h₁, h₂, hu, ht, d, x, h₃, .inr hd, hx⟩

theorem div_denD_eq_sources (C : DCoreSem ImpModule) (l : Linked2) :
    (l.toComp.denD C).div =
      l.irDiv C (l.envDivSrc C) ∪ l.irDiv C (l.nodeDivSrc C) ∪ l.irDiv C (l.chatterSrc C) := by
  rw [← irDiv_union, ← irDiv_union]
  exact Linked2.div_denD_sources C l

/-! ## The session -/

/-- `sessSpec_of`, ending at the idle state the importer's path reaches. -/
theorem sessSpec_of_idle {P : Profile} {l : Linked2} {Ie Ii : SInst} :
    ∀ (ds : List (Linked2.SessRound l Ii)) (calls : List (Fin l.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) {u u' π π' : Store Nat},
      List.Forall₂ (fun d co => (d.j, d.vs) = co.1 ∧ d.ans = co.2.map .vals) ds
        (calls.zip outs) →
      calls.length = outs.length → (∀ d ∈ ds, d.Ok) →
      Ii.Path P (.idle u) (ds.flatMap Linked2.SessRound.instMoves) (.idle u') →
      Linked2.ExpRunT P l Ie π (ds.flatMap fun d => d.dss.flatten) π' →
      Linked2.SessSpec P l Ie Ii u π calls outs u' π'
  | [], calls, outs, u, u', π, π', hF, hlen, _, hp, hrun => by
    cases hrun
    cases hp
    have hz : calls.zip outs = [] := List.forall₂_nil_left_iff.mp hF
    rcases List.zip_eq_nil_iff.mp hz with rfl | rfl
    · have : outs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst this
      exact .nil u π
    · have : calls = [] := List.length_eq_zero_iff.mp hlen
      subst this
      exact .nil u π
  | d :: ds, calls, outs, u, u', π, π', hF, hlen, hOk, hp, hrun => by
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
    have hS := sessSpec_of_idle ds cs os hF'' (by simpa using hlen)
      (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂
    subst hdc
    exact .round d (hOk d List.mem_cons_self) hp₁ hr₁ hans hS

theorem expObs_plays (P : Profile) (l : Linked2) :
    (Linked2.expObs (impSemD P) l).plays =
      ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l) := by
  show Silmaril.Wasm.Component.ext 0 _ (Node.denD (impSemD P) 0 l.expNode).toStrategy = _
  rw [toStrategy_node_denD, forget_impSemD, Linked2.expNode, Node.den]
  rfl

theorem idle_of_path_cplay {I : SInst} {P : Profile} {s : Store Nat} {q : I.HState}
    {ri : List (CRound I.E I.F)} (h : I.Path P (.idle s) (cplay ri) q) : ∃ u, q = .idle u := by
  have := Path.det (ipath_pos h) (path_cplay ri)
  cases q with
  | idle u => exact ⟨u, rfl⟩
  | running f s t => cases this
  | waiting f s t e => cases this

/-- **An IR divergence from the importer's node after a typed session** (under
`Linked2.Adequate`, typed calls and a typed pending call): the session is a specification
session from the instances' stores, and the pending call starts a well-formed round of the
importer, its import calls so far answered by the exporter, at a running state that diverges
host-free. -/
theorem sessDivsB_of_nodeDiv (P : Profile) {l : Linked2} (hl : l.Adequate) {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      l.irDiv (impSemD P) (l.nodeDivSrc (impSemD P))) :
    outs ∈ Linked2.sessDivsB P l calls j vs := by
  obtain ⟨s, t, u, v, h₁, h₂, hu, ht', d, x, h₃, hd, hx⟩ := h
  obtain ⟨sA, tN, hzA, hsA, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := hd
  rw [expObs_plays] at hsA
  -- the pairing runs, so does the layer above it
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) l.expNode.width l.impNode)).div_run
      ⟨ha, .inr haN⟩
  rw [expNode_width] at hb
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₁, htN⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨cl, csP, rfl⟩ := exists_rplay htN
  -- the exporter's environment served all the import calls
  have hAn : NoInl sA := noInl_comp (noInl_ofHandler_pure pure_maskH0) sA hsA
  obtain ⟨rfl, rfl⟩ := serve_run hAn hzA
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
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_run (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at haN
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  rw [halves_rplay_inr] at haN
  -- the importer's node
  rw [div_impNode _ hl.wireTy] at haN
  obtain ⟨uN, vB, hzN, huN, hvB⟩ := haN
  rw [expNode_width] at huN
  obtain ⟨g₂, hvB₂⟩ := (l.imp.toComp.denUD (impSemD P)).div_run hvB
  obtain ⟨up₂, cs₂, rfl⟩ := exists_rplay hvB₂
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨low₂, csP', H₂, H₂', he₂⟩ := hb_zip_run (oneShot_implsH _ _) hyN hzN
  obtain ⟨rfl, rfl, rfl⟩ := rplay_inj he₂
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
  -- the importer's IR
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, sB, tB, F, hpath, hdiv, hf₁, hf₂, hF, hcs⟩ :=
    imp_div_readback hl.impGood hIi htop hck hvB
  obtain ⟨ds, hOk, hr, hcsA, hF', hWT⟩ := build_rounds hl.wireTy (forall₂_comp F G₂) K
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_inv hl.wireTy dss.flatten csP H₂'
  -- the exporter's rounds
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
  have hspec := expEnv_specRoundsT hl.expGood hIe hsA
  obtain ⟨π', hS⟩ := sessRounds_of_specRoundsT hspec fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w, ws, hw, -, -⟩ := hWTall y hy
    show (l.wire.getD y.1.1.val 0) < _
    rw [wire_getD hw]
    exact w.isLt
  have hrun := expRunT_of_sessRounds _ hWTall hS
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunT_split _ _ hrun
  -- the importer's path
  rw [rplay] at hpath
  obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hpath
  obtain ⟨u₁, rfl⟩ := idle_of_path_cplay hp₁
  rw [← hr, LinkedSessionIR.cplay_r] at hp₁
  have hSS := sessSpec_of_idle ds calls outs hF' hlen hOk hp₁ hrun₁
  exact ⟨Ie, Ii, u₁, π, hIe, hIi, hSS, ⟨j, vs, f, ics, dss⟩, sB, tB, π', rfl, rfl,
    ⟨lowerArgs l.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁, hf₂, hF⟩,
    hp₂, hrun₂, hdiv⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
