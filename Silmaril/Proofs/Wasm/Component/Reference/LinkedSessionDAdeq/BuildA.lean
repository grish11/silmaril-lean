module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Build
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.EnvDiv

/-!
# Building the divergences of a linked component: the exporter diverging inside a call

The converse of `EnvDiv.sessDivsA_of_envDiv`: a specification session followed by a round of the
importer calling out on lifted arguments, on which the wired export of the exporter diverges
(`Linked2.sessDivsA`), is an IR divergence.

* **Waiting rounds through the layers**: `hc_wait`, `hb_wait`, `wplay_pair_inr`, the versions of
  `hc_pend`, `hb_pend`, `rplay_pair_inr` at a position waiting on a lower call (the handler below
  forwards it by one call).
* `imp_wait_build`: the converse of `imp_wait_readback`, a finite play of the importer's IR
  waiting on a component import call, from its instance's path to the core import call.
* `exp_layers`, `exp_div_build`: the converse of `exp_div_readback`, the exporter's served calls
  (`ExpRunT`) are complete rounds of its instance through the layers (`LayerI` of
  `SimpleI.ofSimple l.exp`), and a diverging call (`DivAt`) from the store they reach gives a
  divergence of the exporter's environment (through `imp_div_build`, the exporter's node,
  `splitH 0` and `maskH 0`).
* `link_wait_build`: the importer's node and `splitH` on the waiting play.
* `div_denD_of_sessDivsA`: the theorem, through `top_build`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Waiting rounds through the layers -/

section Wait

variable {E F G : Sig.{0}}

/-- **A handler on top of a strategy waiting on the lower call `m`**: `hc_pend`, the lower call
passing through. -/
theorem hc_wait {h : Handler F G} {up : List (CRound E G)} {low : List (CRound E F)}
    (H : HC h up low) {g : G.Op} {f : F.Op} {k : F.Ar f → Prog F (G.Ar g)}
    (hg : h g = .call f k) (cs : List (Round E)) (m : E.Op) :
    ∃ t ∈ Strategy.ofHandler h,
      Zip (rplay low f cs ++ [.inl (.ask m)]) t (rplay up g cs ++ [.inl (.ask m)]) := by
  obtain ⟨t, ht, hz⟩ := hc_pend H hg cs
  exact ⟨t, ht, hz.append_left _⟩

/-- **A handler below a strategy waiting on its lower call `m`**: `hb_pend`, then the handler
forwards `m` by the call `m'`. -/
theorem hb_wait {h : Handler E F} {up : List (CRound F G)} {low : List (CRound E G)}
    (H : HB h up low) (g : G.Op) {cs : List (Round F)} {cs' : List (Round E)}
    (Hc : HRounds h cs cs') {m : F.Op} {m' : E.Op} {k : E.Ar m' → Prog E (F.Ar m)}
    (hm : h m = .call m' k) :
    ∃ t ∈ Strategy.ofHandler h,
      Zip t (rplay up g cs ++ [.inl (.ask m)]) (rplay low g cs' ++ [.inl (.ask m')]) := by
  obtain ⟨t₀, ht₀, hz₀⟩ := H.run
  obtain ⟨t₁, ht₁, hz₁⟩ := Hc.serve (G := G)
  have h₀ := hz₁ (t₁ := [.inr (.ask m), .inl (.ask m')]) (s₁ := [.inl (.ask m)])
    (p₁ := [.inl (.ask m')]) (.sync _ (.left _ .nil))
  refine ⟨t₀ ++ (t₁ ++ [.inr (.ask m), .inl (.ask m')]), Strategy.mem_ofHandler.mpr
    ⟨_, ht₀.append (ht₁.append (.vis (.ask m) (.vis (.call hm) (.nil _))))⟩, ?_⟩
  rw [rplay_snoc_eq, rplay_snoc_eq]
  exact zip_append hz₀ (.right _ h₀)

/-- **The right component of a pairing, waiting on a lower call.** -/
theorem wplay_pair_inr {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (CRound E F₂)} {g : F₂.Op} {cs : List (Round E)} {m : E.Op}
    (h : rplay l g cs ++ [.inl (.ask m)] ∈ σ₂) :
    rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs ++ [.inl (.ask m)] ∈ σ₁.pair σ₂ := by
  refine ⟨⟨_, path_wplay _ _ _ _⟩, ?_, ?_⟩
  · rw [halves_wplay_inr]
    exact σ₁.nil_mem
  · rw [halves_wplay_inr]
    exact h

end Wait

/-! ## The importer, waiting on an import call -/

/-- **The importer's IR waiting on an import call** (the converse of `imp_wait_readback`):
complete rounds through the layers (`LayerI`), then a pending export call `(j, .vals vs)` whose
lowered core question `f`, after core import calls `ics` related to `dss` by `ImpRel`, calls the
core import `e` on arguments that lift to `ws` at the import's type, is a finite play of
`c.toComp.denU (impSem P)` waiting on the component import call `(e, .vals ws)`. -/
theorem imp_wait_build {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    {j : Fin c.exports.length} {vs : List IVal} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {f : I.F.Op}
    (hf₁ : f.1.val = c.exports[j].core) (hf₂ : f.2.1 = xs.map ofFlat)
    {ics : List (Round I.E)} {dss : List (List (Round (sigN c.imports.length)))}
    (hrel : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel c I) ics dss) {e : I.E.Op}
    {nm : String} {ft : FuncTy} {ws : List IVal} (hft : c.imports[e.1.val]? = some (nm, ft))
    (hlw : liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws) {q : I.HState}
    (hpath : I.Path P (.idle I.store) (rplay (L.map LayerI.r) f ics ++ [.inl (.ask e)]) q) :
    rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ++
      [.inl (.ask (e.1.val, .vals ws))] ∈ c.toComp.denU (impSem P) := by
  obtain ⟨cs₂, Hi, Hn⟩ := imp_calls hI hrel
  have hk : c.exports[j].core < c.mod.exports.length := core_lt hc j
  have hke : e.1.val < c.imports.length := (List.getElem?_eq_some_iff.mp hft).1
  have hk' : e.1.val < (CoreModule.imports c.mod).length :=
    lt_of_lt_of_eq e.1.isLt (instNumI hI).imports_length.symm
  have hinst : rplay (L.map LayerI.r) f ics ++ [.inl (.ask e)] ∈ I.strategy P I.store :=
    Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mpr ⟨q, hpath⟩
  -- `core3Sem`'s export handler
  have H₉ : HC (exportH (instNumI hI)) (L.map LayerI.l₁) (L.map LayerI.r) :=
    HC.of_map _ _ L fun d hd =>
      .call (exportH_op hI d.hk d.r.q (hL d hd).core (hL d hd).args) rfl .nil
  obtain ⟨b₉, hb₉, hz₉⟩ := hc_wait H₉ (exportH_op hI hk f hf₁ hf₂) ics e
  -- `core3Sem`'s import handler
  have H₈ : HB (importH (instNumI hI)) (L.map LayerI.l₁) (L.map LayerI.l₂) :=
    HB.of_map _ _ L fun d hd => .cons (hL d hd).imp .nil
  obtain ⟨x₈, hx₈, hz₈⟩ := hb_wait H₈ (⟨c.exports[j].core, hk⟩, .flat xs) Hi
    (m' := (⟨e.1.val, hk'⟩, .flat (e.2.1.filterMap toFlat?)))
    (k := fun r => .pure (payloadAnswer _ r)) rfl
  have hsem : rplay (L.map LayerI.l₂) (⟨c.exports[j].core, hk⟩, .flat xs) cs₂ ++
      [.inl (.ask (⟨e.1.val, hk'⟩, .flat (e.2.1.filterMap toFlat?)))] ∈
      (impSem P).sem c.mod := by
    rw [impSem_sem hI]
    exact ⟨x₈, hx₈, _, ⟨_, hinst, b₉, hb₉, hz₉⟩, hz₈⟩
  -- `widenH`
  have H₇ : HC (widenH (CoreModule.exports c.mod).length) (L.map LayerI.l₃) (L.map LayerI.l₂) :=
    HC.of_map _ _ L fun d _ => .call (h := widenH _) (dite_eq_left d.hk) rfl .nil
  obtain ⟨b₇, hb₇, hz₇⟩ := hc_wait H₇
    (g := (c.exports[j].core, .flat xs)) (f := (⟨c.exports[j].core, hk⟩, .flat xs))
    (dite_eq_left hk) cs₂ (⟨e.1.val, hk'⟩, .flat (e.2.1.filterMap toFlat?))
  -- the `canon lower` wiring
  have H₆ : HB (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) (L.map LayerI.l₃) (L.map LayerI.l₄) :=
    HB.of_map _ _ L fun d hd => .cons (hL d hd).impls .nil
  obtain ⟨u₆, hu₆, hz₆⟩ := hb_wait H₆ (c.exports[j].core, .flat xs) Hn
    (implsN_lower_some hft hk' hke hlw)
  have hN : rplay (L.map LayerI.l₄) (c.exports[j].core, .flat xs) (dss.flatten.map Round.forget)
      ++ [.inl (.ask (e.1.val, .vals ws))] ∈
      coreNode (impSem P) c.imports.length c.mod (SimpleI.lowerArgs c.imports) :=
    ⟨u₆, hu₆, _, ⟨_, hsem, b₇, hb₇, hz₇⟩, hz₆⟩
  -- `splitH` and the pairing
  have H₅ : HC (splitH c.imports.length) (L.map LayerI.l₅)
      ((L.map LayerI.l₄).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift _ _ _) rfl .nil
  obtain ⟨b₅, hb₅, hz₅⟩ := hc_wait H₅ (splitH_shift c.imports.length c.exports[j].core (.flat xs))
    (dss.flatten.map Round.forget) (e.1.val, .vals ws)
  -- the import mask
  have H₄ : HB (maskH c.imports.length) (L.map LayerI.l₅) (L.map LayerI.l₅) :=
    HB.of_map _ _ L fun d _ => .cons (hrounds_maskH _ _) .nil
  obtain ⟨s₄, hs₄, hz₄⟩ := hb_wait H₄ (c.exports[j].core + c.imports.length, .flat xs)
    (hrounds_maskH _ dss.flatten) (m' := (e.1.val, .vals ws)) (k := fun r => .pure r)
    (ite_eq_left hke)
  have hE : rplay (L.map LayerI.l₅) (c.exports[j].core + c.imports.length, .flat xs)
      (dss.flatten.map Round.forget) ++ [.inl (.ask (e.1.val, .vals ws))] ∈
      envSI (impSem P) c :=
    ⟨s₄, hs₄, _, ⟨_, wplay_pair_inr hN, b₅, hb₅, hz₅⟩, hz₄⟩
  -- the export handler
  have H₃ : HC (exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports)
      (L.map LayerI.l₆) (L.map LayerI.l₅) := by
    refine HC.of_map _ _ L fun d hd => ?_
    have hl' : checkLower c.exports[d.j.val].ty.params d.vs = some d.xs := (hL d hd).lower
    refine .call (h := exportsH _ _)
      (q' := (c.exports[d.j].core + c.imports.length, .flat d.xs))
      (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[d.j].ty)))) ?_ rfl .nil
    rw [exportsH_toCompI c d.j.isLt d.vs d.hk, hl']
    rfl
  have hg₃ : exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports
      (j.val, .vals vs) = .call (c.exports[j].core + c.imports.length, .flat xs)
        fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))) := by
    have hl' : checkLower c.exports[j.val].ty.params vs = some xs := hl
    rw [exportsH_toCompI c j.isLt vs hk, hl']
    rfl
  obtain ⟨t₃, ht₃, hz₃⟩ := hc_wait H₃ hg₃ (dss.flatten.map Round.forget) (e.1.val, .vals ws)
  rw [denU_toCompI]
  exact ⟨_, hE, t₃, ht₃, hz₃⟩

/-! ## The exporter -/

section Exp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- **The exporter's served calls as rounds through the layers**: import calls answered by the
exporter's specification from a well-formed store `s` to `s'` (`ExpRunT`), renamed to the wired
exports, are complete rounds of its instance from `s` to `s'`, through the layers of
`SimpleI.ofSimple l.exp` (no import calls). -/
theorem exp_layers {P : Profile} {l : Linked2} (hc : l.exp.Good) {I : SInst}
    (hI : l.exp.mod.IsInst I) :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      Linked2.ExpRunT P l I s ds s' → I.WellFormed s →
      ∃ L : List (LayerI (SimpleI.ofSimple l.exp) I), (∀ d ∈ L, d.Ok (isInst_ofSimple hI)) ∧
        I.Path P (.idle s) (cplay (L.map LayerI.r)) (.idle s') ∧
        L.map LayerI.l₆ = (ds.map (wireRound l)).map mk0
  | _, _, _, .nil _, _ => ⟨[], (fun _ h => nomatch h), .nil _, rfl⟩
  | s, _, _, .ret (s₁ := s₁) (k := k) (ws := ws) (us := us) w hw hret hrun, hwf => by
    obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem w.isLt)
    obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
    have hxs : (lowerArgs l.exp.exports[w].ty.params ws).map (·.type) =
        l.exp.mod.exports[l.exp.exports[w].core].2.params := by
      rw [show l.exp.mod.exports[l.exp.exports[w].core] = (nm, l.exp.exports[w].ty.flat)
        from hget]
      exact lowerList_types _ _ hret.typed
    obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := hret.run
    have steps : Steps P Det.noHost (invoke s (I.addrs.getD l.exp.exports[w].core 0)
        ((lowerArgs l.exp.exports[w].ty.params ws).map ofFlat)) (t'.config s₁) :=
      internalP_steps (H := Nat) run
    obtain ⟨wa, hwa⟩ := answer_at hI hwf hk hxs steps (r := .values cvs) final
    have hp₁ : I.Path P (.idle s)
        [.inr (.ask (opAt hI hk hxs)), .inr (.ans (opAt hI hk hxs) wa)] (.idle s₁) :=
      .cons (.call s _) (.cons (.oret run final hwa) (.nil _))
    have hpay : answerPayload wa = some (.flat ys) := by
      rw [answerPayload_of_ofResult? hwa]
      simp only [hys, Option.map_some]
    have hup : (some (Payload.flat ys)).bind (Adapter.up (.lift l.exp.exports[w].ty)) =
        some (.vals us) := by
      simp only [Option.bind_some, Adapter.up, hws, Option.map_some]
    have hwf' := hret.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨L, hL, hpL, hmL⟩ := exp_layers hc hI hrun hwf'
    let d : LayerI (SimpleI.ofSimple l.exp) I :=
      ⟨⟨opAt hI hk hxs, [], wa⟩, w, ws, lowerArgs l.exp.exports[w].ty.params ws, hk, [], []⟩
    have hans : d.ans = some (.vals us) := by
      show (answerPayload wa).bind (Adapter.up (.lift l.exp.exports[w].ty)) = _
      rw [hpay]
      exact hup
    refine ⟨d :: L, ?_, path_append hp₁ hpL, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨checkLower_of_check hret.typed, rfl, rfl, .nil, .nil⟩
      · exact hL d' hd'
    · rw [List.map_cons, List.map_cons, List.map_cons, hmL]
      congr 1
      show (⟨(w.val, .vals ws), [], d.ans⟩ : CRound sigU sigU) =
        ⟨(l.wire.getD k.val 0, .vals ws), [], some (.vals us)⟩
      rw [hans, wire_getD hw]
  | s, _, _, .trap (s₁ := s₁) (k := k) (ws := ws) w hw htrap hrun, hwf => by
    obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem w.isLt)
    obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
    have hxs : (lowerArgs l.exp.exports[w].ty.params ws).map (·.type) =
        l.exp.mod.exports[l.exp.exports[w].core].2.params := by
      rw [show l.exp.mod.exports[l.exp.exports[w].core] = (nm, l.exp.exports[w].ty.flat)
        from hget]
      exact lowerList_types _ _ htrap.typed
    obtain ⟨t', res, run, final, htr⟩ := htrap.run
    have steps : Steps P Det.noHost (invoke s (I.addrs.getD l.exp.exports[w].core 0)
        ((lowerArgs l.exp.exports[w].ty.params ws).map ofFlat)) (t'.config s₁) :=
      internalP_steps (H := Nat) run
    obtain ⟨wa, hwa⟩ := answer_at hI hwf hk hxs steps (r := res) final
    have hp₁ : I.Path P (.idle s)
        [.inr (.ask (opAt hI hk hxs)), .inr (.ans (opAt hI hk hxs) wa)] (.idle s₁) :=
      .cons (.call s _) (.cons (.oret run final hwa) (.nil _))
    have hpay : answerPayload wa = (coreRes res).map .flat := by
      rw [answerPayload_of_ofResult? hwa]
      cases res <;> rfl
    have hwf' := htrap.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨L, hL, hpL, hmL⟩ := exp_layers hc hI hrun hwf'
    let d : LayerI (SimpleI.ofSimple l.exp) I :=
      ⟨⟨opAt hI hk hxs, [], wa⟩, w, ws, lowerArgs l.exp.exports[w].ty.params ws, hk, [], []⟩
    have hans : d.ans = none := by
      show (answerPayload wa).bind (Adapter.up (.lift l.exp.exports[w].ty)) = _
      rw [hpay]
      exact up_none_of_traps htr
    refine ⟨d :: L, ?_, path_append hp₁ hpL, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨checkLower_of_check htrap.typed, rfl, rfl, .nil, .nil⟩
      · exact hL d' hd'
    · rw [List.map_cons, List.map_cons, List.map_cons, hmL]
      congr 1
      show (⟨(w.val, .vals ws), [], d.ans⟩ : CRound sigU sigU) =
        ⟨(l.wire.getD k.val 0, .vals ws), [], none⟩
      rw [hans, wire_getD hw]

/-- **A divergence of the exporter's environment from its specification** (the converse of
`exp_div_readback`): import calls `ds` answered by the exporter's specification from its
instance's store to `π`, renamed to the wired exports, then a call of export `w` on `ws`
diverging from `π`, are a divergence of the exporter's environment. -/
theorem exp_div_build {P : Profile} {l : Linked2} (hl : l.Adequate) {Ie : SInst}
    (hIe : l.exp.mod.IsInst Ie) {ds : List (Round (sigN l.imp.imports.length))} {π : Store Nat}
    (hrun : Linked2.ExpRunT P l Ie Ie.store ds π) {w : Fin l.exp.exports.length}
    {ws : List IVal} (hdiv : DivAt P Ie l.exp.exports[w] ws π) :
    twos (ds.map (wireRound l)) ++ [.inr (.ask (w.val, .vals ws))] ∈
      (Linked2.expObs (impSemD P) l).div := by
  obtain ⟨L, hL, hpL, hmL⟩ := exp_layers hl.expGood hIe hrun hIe.1.choose_spec.ok
  obtain ⟨nm, hcore⟩ := hl.expGood.core _ (List.getElem_mem w.isLt)
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs l.exp.exports[w].ty.params ws).map (·.type) =
      l.exp.mod.exports[l.exp.exports[w].core].2.params := by
    rw [show l.exp.mod.exports[l.exp.exports[w].core] = (nm, l.exp.exports[w].ty.flat)
      from hget]
    exact lowerList_types _ _ hdiv.typed
  obtain ⟨g, hg₀, hg⟩ := hdiv.run
  have hpath : Ie.Path P (.idle Ie.store) (rplay (L.map LayerI.r) (opAt hIe hk hxs) [])
      (.running (opAt hIe hk hxs) π (Ie.initThread (opAt hIe hk hxs))) :=
    path_append hpL (.cons (.call π _) (.nil _))
  have hB : Linked2.DivB P π (Ie.initThread (opAt hIe hk hxs)) :=
    ⟨g, by rw [hg₀, initThread_eq (c := l.exp) (j := w) (vs := ws) rfl rfl], hg⟩
  have hv := imp_div_build (good_ofSimple hl.expGood) (isInst_ofSimple hIe) hL (j := w) (vs := ws)
    (checkLower_of_check hdiv.typed) (f := opAt hIe hk hxs) rfl rfl (dss := []) .nil hpath hB
  rw [hmL] at hv
  -- the exporter's node
  have HI : HB (implsH 0 []) ((ds.map (wireRound l)).map (mk0 (E := sigU)))
      ((ds.map (wireRound l)).map mk0) :=
    HB.of_map mk0 mk0 _ fun _ _ => .cons .nil .nil
  obtain ⟨uI, huI, hzI⟩ := hb_pend HI (w.val, .vals ws) .nil
  have hN : rplay ((ds.map (wireRound l)).map mk0) (w.val, .vals ws) [] ∈
      (Node.denD (impSemD P) 0 l.expNode).div := by
    rw [Linked2.expNode, div_node_inst]
    exact .inl ⟨uI, _, hzI, huI, hv⟩
  -- `splitH 0` and `maskH 0`
  have HS : HC (splitH 0) ((ds.map (wireRound l)).map (mk0 (E := sigU)))
      (((ds.map (wireRound l)).map mk0).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map (g := CRound.inr (F₁ := sigU))]
    exact HC.of_map (mk0 (E := sigU)) (CRound.inr ∘ mk0) _ fun (r : Round sigU) _ =>
      .call (h := splitH 0) (splitH_shift 0 r.1.1 r.1.2) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_pend HS (splitH_shift 0 w.val (.vals ws)) []
  have HM : HB (maskH 0) ((ds.map (wireRound l)).map (mk0 (E := sigU)))
      ((ds.map (wireRound l)).map mk0) :=
    HB.of_map mk0 mk0 _ fun _ _ => .cons .nil .nil
  obtain ⟨sM, hsM, hzM⟩ := hb_pend HM (w.val, .vals ws) .nil
  rw [← rplay_mk0]
  exact .inl (.inr ⟨sM, _, hzM, hsM, _, bS, hzS,
    ⟨rplay_pair_inr ((Node.denD (impSemD P) 0 l.expNode).div_mem hN),
      by rw [halves_rplay_inr]; exact hN⟩, hbS⟩)

end Exp

/-! ## The linked component -/

section Linked

variable {P : Profile} {l : Linked2} {Ii : SInst}

/-- **The importer's node and `splitH`, waiting on an import call**: a finite play of the
importer's IR waiting on its import call `k` (wired to the export `w` of the exporter) is, with
the import calls renamed, a finite play of the node layer above the exporter's environment,
waiting on the call of `w`. -/
theorem link_wait_build {L : List (LayerI l.imp Ii)} {j : Fin l.imp.exports.length}
    {vs : List IVal} {dss : List (List (Round (sigN l.imp.imports.length)))} {k : Nat}
    {ws : List IVal}
    (hvB : rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ++
      [.inl (.ask (k, .vals ws))] ∈ l.imp.toComp.denU (impSem P))
    {w : Fin l.exp.exports.length} (hw : l.wire[k]? = some w.val)
    (hall : ∀ x ∈ (L.flatMap fun d => d.dss.flatten) ++ dss.flatten,
      ∃ w : Fin l.exp.exports.length, l.wire[x.1.1.val]? = some w.val) :
    rplay (L.map LayerI.wired) (l.exp.exports.length + j.val, .vals vs)
      (dss.flatten.map (wireRound l)) ++ [.inl (.ask (w.val, .vals ws))] ∈
      (DStrategy.extTop l.expNode.width
        (Node.denD (impSemD P) l.expNode.width l.impNode)).toStrategy := by
  -- the importer's node forwards the import calls
  have HN : HB (implsH l.exp.exports.length (wireArgs l)) (L.map LayerI.l₆)
      (L.map LayerI.wiredN) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wire fun x hx =>
      hall x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hx⟩))) .nil
  obtain ⟨uN, huN, hzN⟩ := hb_wait HN (j.val, .vals vs)
    (hrounds_wire fun x hx => hall x (List.mem_append_right _ hx)) (implsH_wire hw (.vals ws))
  have hNB : rplay (L.map LayerI.wiredN) (j.val, .vals vs) (dss.flatten.map (wireRound l)) ++
      [.inl (.ask (w.val, .vals ws))] ∈
      (Node.denD (impSemD P) l.expNode.width l.impNode).toStrategy := by
    rw [toStrategy_node_denD, forget_impSemD, Linked2.impNode, Node.den, expNode_width]
    exact ⟨uN, huN, _, hvB, hzN⟩
  -- `splitH` and the pairing
  have HS : HC (splitH l.exp.exports.length) (L.map LayerI.wired)
      ((L.map LayerI.wiredN).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_wait HS (splitH_shift' l.exp.exports.length j.val (.vals vs))
    (dss.flatten.map (wireRound l)) (w.val, .vals ws)
  refine ⟨_, wplay_pair_inr hNB, bS, ?_, hzS⟩
  rw [expNode_width]
  exact hbS

end Linked

/-! ## The theorem -/

/-- **A round of the exporter diverging inside an import call is an IR divergence** (every
profile, under `Linked2.Adequate`): after a specification session of `calls` with the outcomes
`outs`, a round of the importer on export `j` and `vs`, its import calls so far answered by the
exporter, then an import call on lifted arguments on which the wired export of the exporter
diverges, is an IR divergence after `sessMoves calls outs` on the pending call. -/
theorem div_denD_of_sessDivsA (P : Profile) {l : Linked2} (hl : l.Adequate)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : outs ∈ Linked2.sessDivsA P l calls j vs) :
    Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD P)).div := by
  obtain ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, rfl, rfl, hOk, hp, hr,
    e, s', t', nm, ft, ws, w, hpe, hft, hlw, hwk, hdivAt⟩ := h
  obtain ⟨L, hL, hpL, hrL, hm⟩ := LinkedSessionRef.sessSpec_rounds hS
  obtain ⟨LL, hLL, e₁, e₂⟩ := layers_of hl.impGood hIi (LinkedSessionIR.rel_u hL)
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOk
  -- the importer, waiting on the import call
  have hpath : Ii.Path P (.idle Ii.store) (rplay (LL.map LayerI.r) d.f d.cs ++ [.inl (.ask e)])
      (.waiting d.f s' t' e) := by
    rw [rplay, e₁, LinkedSessionIR.cplay_r]
    exact path_append (path_append hpL hp) hpe
  have hvB := imp_wait_build hl.impGood hIi hLL hxs hf₁ hf₂ hrel hft hlw hpath
  -- the exporter's run, then its diverging call
  have hcs : (LL.flatMap fun d => d.dss.flatten) = L.flatMap fun d => d.dss.flatten := by
    rw [← LinkedSessionIR.flatMap_u_cs, ← e₂, List.flatMap_map]
    rfl
  have hrun : Linked2.ExpRunT P l Ie Ie.store
      ((LL.flatMap fun d => d.dss.flatten) ++ d.dss.flatten) π₁ := by
    rw [hcs]
    exact LinkedSessionRef.expRunT_append hrL hr
  have hA := exp_div_build hl hIe hrun hdivAt
  have htN := link_wait_build hvB hwk (LinkedSessionIR.expRunT_wire hrun)
  -- the environment serves the import calls, then diverges on the pending one
  have hz := zip_append (zip_serve_pend (E := sigU) (LL.map LayerI.wired)
    (l.exp.exports.length + d.j.val, .vals d.vs) (d.dss.flatten.map (wireRound l)))
    (.sync (Ev.ask (w.val, Payload.vals ws)) .nil)
  rw [List.append_nil, flatMap_wired, ← List.map_append] at hz
  have hd : rplay ((LL.map LayerI.wired).map (CRound.hide (E := sigU)))
      (l.exp.exports.length + d.j.val, .vals d.vs) [] ∈ l.envDivSrc (impSemD P) := by
    exact ⟨_, _, hz, hA, htN⟩
  have hX := top_build (P := P) hd
  have hplay : rplay ((LL.map LayerI.u).map (Linked2.linkRound l)) (l.topQ d.j d.vs) [] =
      Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ d.j d.vs))] := by
    rw [rplay, e₂, LinkedSessionIR.cplay_link, hm]
    rfl
  rw [hplay] at hX
  rw [div_denD_eq_sources]
  exact .inl (.inl hX)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
