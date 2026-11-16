module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Linked
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.IR

/-!
# Building the divergences of a linked component: the importer diverging host-free

The converse of `Linked.sessDivsB_of_nodeDiv`: a specification session followed by a round of
the importer diverging host-free (`Linked2.sessDivsB`) is an IR divergence.

* **Pending rounds through the layers** (the pending versions of `cplay_comp_ofHandler`,
  `cplay_ofHandler_comp`, `cplay_comp_serve`, `cplay_pair_inr`), stated on the `Zip` witnesses,
  so that they build the witnesses of the divergence theorems: `hc_pend` (a handler on top
  forwards the pending question by one call), `hb_pend` (a handler below serves the pending
  round's lower calls), `zip_serve_pend` (a server below answers them without calls of its own),
  `rplay_pair_inr` (the right component of a pairing).
* `imp_div_build`: the converse of `imp_div_readback`, the importer's IR divergence from its
  instance's path to a `DivB` state, through the layers of `SimpleI.div_denUD_impSemD` and
  `SimpleI.div_coreNode_impSemD` (the layers of `layers_sem`, `layers_env`, `layers_denU`).
* `link_div_build`: the converse of the read-back in `sessDivsB_of_nodeDiv`, through the
  importer's node (`div_impNode`), the exporter's environment serving all the import calls
  (`expEnv_rounds`), `splitH`, and the outer handlers (the layers of `link_layersT` and
  `linked_seq_denT`).
* `div_denD_of_sessDivsB`: the theorem.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.SingleThreaded (ofFlat Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Pending rounds through the layers -/

section Pend

variable {E F G : Sig.{0}}

/-- **A handler on top, with a pending round**: the complete rounds `HC h up low`, then the
pending question `g` forwarded by one call `f`, its lower calls `cs` passing through. -/
theorem hc_pend {h : Handler F G} {up : List (CRound E G)} {low : List (CRound E F)}
    (H : HC h up low) {g : G.Op} {f : F.Op} {k : F.Ar f → Prog F (G.Ar g)}
    (hg : h g = .call f k) (cs : List (Round E)) :
    ∃ t ∈ Strategy.ofHandler h, Zip (rplay low f cs) t (rplay up g cs) := by
  obtain ⟨t, ht, hz⟩ := H.run
  have h₀ := zip_calls_left (E := E) (F := F) (G := G) .nil cs
  simp only [List.append_nil] at h₀
  exact ⟨t ++ [.inr (.ask g), .inl (.ask f)],
    Strategy.mem_ofHandler.mpr ⟨_, ht.append (.vis (.ask g) (.vis (.call hg) (.nil _)))⟩,
    zip_append hz (.right _ (.sync _ h₀))⟩

/-- **A handler below, with a pending round**: the complete rounds `HB h up low`, then the
pending question `g`, its lower calls `cs` served by `h` by the calls `cs'`. -/
theorem hb_pend {h : Handler E F} {up : List (CRound F G)} {low : List (CRound E G)}
    (H : HB h up low) (g : G.Op) {cs : List (Round F)} {cs' : List (Round E)}
    (Hc : HRounds h cs cs') :
    ∃ t ∈ Strategy.ofHandler h, Zip t (rplay up g cs) (rplay low g cs') := by
  obtain ⟨t₀, ht₀, hz₀⟩ := H.run
  obtain ⟨t₁, ht₁, hz₁⟩ := Hc.serve (G := G)
  have h₀ := hz₁ (t₁ := []) (s₁ := []) (p₁ := []) .nil
  simp only [List.append_nil] at h₀
  exact ⟨t₀ ++ t₁, Strategy.mem_ofHandler.mpr ⟨_, ht₀.append ht₁⟩, zip_append hz₀ (.right _ h₀)⟩

/-- **A server below, with a pending round**: the lower calls of the rounds `l` and of the
pending round, answered by complete rounds of the strategy below, are hidden. -/
theorem zip_serve_pend (l : List (CRound F G)) (g : G.Op) (cs : List (Round F)) :
    Zip (twos (E := E) (l.flatMap (·.cs) ++ cs)) (rplay l g cs)
      (rplay (l.map CRound.hide) g []) := by
  have h₀ := zip_twos_calls (E := E) (F := F) (G := G) .nil cs
  simp only [List.append_nil] at h₀
  rw [twos_append]
  exact zip_append (zip_serve l) (.right _ h₀)

/-- **The right component of a pairing, with a pending round.** -/
theorem rplay_pair_inr {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (CRound E F₂)} {g : F₂.Op} {cs : List (Round E)} (h : rplay l g cs ∈ σ₂) :
    rplay (l.map (CRound.inr (F₁ := F₁))) (.inr g) cs ∈ σ₁.pair σ₂ := by
  refine ⟨⟨_, path_rplay _ _ _⟩, ?_, ?_⟩
  · rw [halves_rplay_inr]
    exact σ₁.nil_mem
  · rw [halves_rplay_inr]
    exact h

end Pend

/-! ## The importer -/

/-- **The importer's IR divergence from its instance** (the converse of `imp_div_readback`):
complete rounds through the layers (`LayerI`), then a pending export call `(j, .vals vs)` whose
lowered core question `f` is pending after core import calls `ics` related to `dss` by `ImpRel`,
at a running state that diverges host-free, is a divergence of `c.toComp.denUD (impSemD P)`. -/
theorem imp_div_build {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    {j : Fin c.exports.length} {vs : List IVal} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {f : I.F.Op}
    (hf₁ : f.1.val = c.exports[j].core) (hf₂ : f.2.1 = xs.map ofFlat)
    {ics : List (Round I.E)} {dss : List (List (Round (sigN c.imports.length)))}
    (hrel : List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel c I) ics dss) {s : Store Nat} {t : Thread}
    (hpath : I.Path P (.idle I.store) (rplay (L.map LayerI.r) f ics) (.running f s t))
    (hdiv : Linked2.DivB P s t) :
    rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ∈
      ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).div := by
  obtain ⟨cs₂, Hi, Hn⟩ := imp_calls hI hrel
  have hk : c.exports[j].core < c.mod.exports.length := core_lt hc j
  -- `core3Sem`'s export handler
  have H₉ : HC (exportH (instNumI hI)) (L.map LayerI.l₁) (L.map LayerI.r) :=
    HC.of_map _ _ L fun d hd =>
      .call (exportH_op hI d.hk d.r.q (hL d hd).core (hL d hd).args) rfl .nil
  obtain ⟨b₉, hb₉, hz₉⟩ := hc_pend H₉ (exportH_op hI hk f hf₁ hf₂) ics
  -- `core3Sem`'s import handler
  have H₈ : HB (importH (instNumI hI)) (L.map LayerI.l₁) (L.map LayerI.l₂) :=
    HB.of_map _ _ L fun d hd => .cons (hL d hd).imp .nil
  obtain ⟨x₈, hx₈, hz₈⟩ := hb_pend H₈ (⟨c.exports[j].core, hk⟩, .flat xs) Hi
  -- `widenH`
  have H₇ : HC (widenH (CoreModule.exports c.mod).length) (L.map LayerI.l₃) (L.map LayerI.l₂) :=
    HC.of_map _ _ L fun d _ => .call (h := widenH _) (dite_eq_left d.hk) rfl .nil
  obtain ⟨b₇, hb₇, hz₇⟩ := hc_pend H₇
    (g := (c.exports[j].core, .flat xs)) (f := (⟨c.exports[j].core, hk⟩, .flat xs))
    (dite_eq_left hk) cs₂
  -- the `canon lower` wiring
  have H₆ : HB (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) (L.map LayerI.l₃) (L.map LayerI.l₄) :=
    HB.of_map _ _ L fun d hd => .cons (hL d hd).impls .nil
  obtain ⟨u₆, hu₆, hz₆⟩ := hb_pend H₆ (c.exports[j].core, .flat xs) Hn
  -- the core node
  have hN : rplay (L.map LayerI.l₄) (c.exports[j].core, .flat xs) (dss.flatten.map Round.forget) ∈
      (Node.denD (impSemD P) c.imports.length c.coreNode).div := by
    rw [div_coreNode_inst P _ c hI]
    exact ⟨u₆, _, hz₆, hu₆, _, b₇, hz₇, ⟨x₈, _, hz₈, hx₈, _, b₉, hz₉, ⟨f, s, t, hpath, hdiv⟩,
      hb₉⟩, hb₇⟩
  -- `splitH` and the pairing
  have H₅ : HC (splitH c.imports.length) (L.map LayerI.l₅)
      ((L.map LayerI.l₄).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift _ _ _) rfl .nil
  obtain ⟨b₅, hb₅, hz₅⟩ := hc_pend H₅ (splitH_shift c.imports.length c.exports[j].core (.flat xs))
    (dss.flatten.map Round.forget)
  -- the import mask
  have H₄ : HB (maskH c.imports.length) (L.map LayerI.l₅) (L.map LayerI.l₅) :=
    HB.of_map _ _ L fun d _ => .cons (hrounds_maskH _ _) .nil
  obtain ⟨s₄, hs₄, hz₄⟩ := hb_pend H₄ (c.exports[j].core + c.imports.length, .flat xs)
    (hrounds_maskH _ dss.flatten)
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
  obtain ⟨t₃, ht₃, hz₃⟩ := hc_pend H₃ hg₃ (dss.flatten.map Round.forget)
  rw [SimpleI.div_denUD_impSemD P c ⟨I, hI⟩]
  exact ⟨_, t₃, hz₃, ⟨s₄, _, hz₄, hs₄, _, b₅, hz₅,
    ⟨rplay_pair_inr ((Node.denD (impSemD P) c.imports.length c.coreNode).div_mem hN),
      by rw [halves_rplay_inr]; exact hN⟩, hb₅⟩, ht₃⟩

/-! ## The linked component -/

section Linked

variable {P : Profile} {l : Linked2} {Ii : SInst}

/-- An importer round with its import calls renamed to the wired exports, below `splitH`. -/
def LayerI.wiredN (d : LayerI l.imp Ii) : CRound sigU sigU :=
  ⟨(d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l), d.ans⟩

/-- An importer round as a round of the linked environment, without lower calls. -/
def LayerI.env (d : LayerI l.imp Ii) : CRound sigU sigU :=
  ⟨(d.j.val, .vals d.vs), [], d.ans⟩

/-- An importer round as a round below `narrowH`. -/
def LayerI.top (d : LayerI l.imp Ii) : CRound l.toComp.imports.sig sigU :=
  ⟨(d.j.val, .vals d.vs), [], d.ans⟩

/-- **The outer handlers on a pending linked call** (the layers of `link_layersT` and
`linked_seq_denT` above the environment): a divergence `S` of the linked environment on the
pending call of environment function `exp.exports.length + j`, after the importer's complete
rounds `L` with their import calls hidden, is an IR divergence on the pending call `topQ j vs`
built from `S`. -/
theorem top_build {S : Set (List (Move sigU sigU))} {L : List (LayerI l.imp Ii)}
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hd : rplay ((L.map LayerI.wired).map (CRound.hide (E := sigU)))
      (l.exp.exports.length + j.val, .vals vs) [] ∈ S) :
    rplay ((L.map LayerI.u).map (Linked2.linkRound l)) (l.topQ j vs) [] ∈
      l.irDiv (impSemD P) S := by
  -- the linked export handler
  have HE : HC (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)
      (L.map LayerI.env) ((L.map LayerI.wired).map (CRound.hide (E := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ =>
      .call (h := exportsH _ _) (q := (d.j.val, .vals d.vs))
        (q' := (l.exp.exports.length + d.j.val, .vals d.vs)) (k := fun n => .pure n)
        (exportsH_toCompL l d.j.isLt _) rfl .nil
  obtain ⟨xE, hxE, hzE⟩ := hc_pend HE (exportsH_toCompL l j.isLt (.vals vs)) []
  have hxE' : xE ∈ Strategy.ofHandler
      (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports) := by
    rw [envAfter_link]
    exact hxE
  -- `widenH 0` and `narrowH`
  have HW : HB (widenH 0) (L.map LayerI.env) (L.map LayerI.top) :=
    HB.of_map _ _ L fun _ _ => .cons .nil .nil
  obtain ⟨uW, huW, hzW⟩ := hb_pend HW (j.val, .vals vs) .nil
  have HT : HC (narrowH l.toComp.exports.length) ((L.map LayerI.u).map (Linked2.linkRound l))
      (L.map LayerI.top) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun _ _ => .call (h := narrowH _) rfl rfl .nil
  obtain ⟨tT, htT, hzT⟩ := hc_pend HT (g := l.topQ j vs) (f := (j.val, .vals vs)) rfl []
  exact ⟨_, tT, uW, _, hzW, hzT, huW, htT, _, xE, hzE, hd, hxE'⟩

/-- **The linked IR divergence from the importer's** (the converse of the read-back of
`sessDivsB_of_nodeDiv`): complete rounds of the importer through the layers (`LayerI`) and a
pending call of its export `j` on `vs`, on which its IR diverges after the import calls `dss`,
all import calls being answered by the exporter's specification from its instance's store, are
an IR divergence of the linked component coming from the importer's node. -/
theorem link_div_build (hl : l.Adequate) {Ie : SInst} (hIe : l.exp.mod.IsInst Ie)
    {L : List (LayerI l.imp Ii)} {j : Fin l.imp.exports.length} {vs : List IVal}
    {dss : List (List (Round (sigN l.imp.imports.length)))}
    (hvB : rplay (L.map LayerI.l₆) (j.val, .vals vs) (dss.flatten.map Round.forget) ∈
      (l.imp.toComp.denUD (impSemD P)).div) {π' : Store Nat}
    (hrun : Linked2.ExpRunT P l Ie Ie.store ((L.flatMap fun d => d.dss.flatten) ++ dss.flatten)
      π') :
    rplay ((L.map LayerI.u).map (Linked2.linkRound l)) (l.topQ j vs) [] ∈
      l.irDiv (impSemD P) (l.nodeDivSrc (impSemD P)) := by
  have hall := LinkedSessionIR.expRunT_wire hrun
  -- the exporter's environment serves all the import calls
  obtain ⟨li, lc, hli, H, X⟩ := LinkedSessionIR.expRunT_mem hl.expGood hIe hrun
    hIe.1.choose_spec.ok
  have hexp : twos (((L.flatMap fun d => d.dss.flatten) ++ dss.flatten).map (wireRound l)) ∈
      (Linked2.expObs (impSemD P) l).plays := by
    rw [expObs_plays]
    exact expEnv_rounds hIe hli H X
  -- the importer's node forwards them
  have HN : HB (implsH l.exp.exports.length (wireArgs l)) (L.map LayerI.l₆)
      (L.map LayerI.wiredN) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wire fun x hx =>
      hall x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hx⟩))) .nil
  obtain ⟨uN, huN, hzN⟩ := hb_pend HN (j.val, .vals vs)
    (hrounds_wire fun x hx => hall x (List.mem_append_right _ hx))
  have hNB : rplay (L.map LayerI.wiredN) (j.val, .vals vs) (dss.flatten.map (wireRound l)) ∈
      (Node.denD (impSemD P) l.expNode.width l.impNode).div := by
    rw [div_impNode _ hl.wireTy]
    refine ⟨uN, _, hzN, ?_, hvB⟩
    rw [expNode_width]
    exact huN
  -- `splitH` and the pairing
  have HS : HC (splitH l.exp.exports.length) (L.map LayerI.wired)
      ((L.map LayerI.wiredN).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil
  obtain ⟨bS, hbS, hzS⟩ := hc_pend HS (splitH_shift' l.exp.exports.length j.val (.vals vs))
    (dss.flatten.map (wireRound l))
  -- the source: the importer's node diverges
  have hd : rplay ((L.map LayerI.wired).map (CRound.hide (E := sigU)))
      (l.exp.exports.length + j.val, .vals vs) [] ∈ l.nodeDivSrc (impSemD P) := by
    refine ⟨_, _, zip_serve_pend (L.map LayerI.wired) _ (dss.flatten.map (wireRound l)), ?_,
      _, bS, hzS, ⟨rplay_pair_inr
        ((Node.denD (impSemD P) l.expNode.width l.impNode).div_mem hNB),
        by rw [halves_rplay_inr]; exact hNB⟩, ?_⟩
    · rw [flatMap_wired, ← List.map_append]
      exact hexp
    · rw [expNode_width]
      exact hbS
  exact top_build hd

end Linked

/-! ## The theorem -/

/-- **A round of the importer diverging host-free is an IR divergence** (every profile, under
`Linked2.Adequate`): after a specification session of `calls` with the outcomes `outs`, a round
of the importer on export `j` and `vs`, its import calls so far answered by the exporter, at a
running state that diverges host-free, is an IR divergence after `sessMoves calls outs` on the
pending call. -/
theorem div_denD_of_sessDivsB (P : Profile) {l : Linked2} (hl : l.Adequate)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : outs ∈ Linked2.sessDivsB P l calls j vs) :
    Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD P)).div := by
  obtain ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, rfl, rfl, hOk, hp, hr, hB⟩ := h
  obtain ⟨L, hL, hpL, hrL, hm⟩ := LinkedSessionRef.sessSpec_rounds hS
  obtain ⟨LL, hLL, e₁, e₂⟩ := layers_of hl.impGood hIi (LinkedSessionIR.rel_u hL)
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOk
  have hpath : Ii.Path P (.idle Ii.store) (rplay (LL.map LayerI.r) d.f d.cs)
      (.running d.f s t) := by
    rw [rplay, e₁, LinkedSessionIR.cplay_r]
    exact path_append hpL hp
  have hvB := imp_div_build hl.impGood hIi hLL hxs hf₁ hf₂ hrel hpath hB
  have hcs : (LL.flatMap fun d => d.dss.flatten) = L.flatMap fun d => d.dss.flatten := by
    rw [← LinkedSessionIR.flatMap_u_cs, ← e₂, List.flatMap_map]
    rfl
  have hrun : Linked2.ExpRunT P l Ie Ie.store
      ((LL.flatMap fun d => d.dss.flatten) ++ d.dss.flatten) π₁ := by
    rw [hcs]
    exact LinkedSessionRef.expRunT_append hrL hr
  have hX := link_div_build hl hIe hvB hrun
  have hplay : rplay ((LL.map LayerI.u).map (Linked2.linkRound l)) (l.topQ d.j d.vs) [] =
      Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ d.j d.vs))] := by
    rw [rplay, e₂, LinkedSessionIR.cplay_link, hm]
    rfl
  rw [hplay] at hX
  rw [div_denD_eq_sources]
  exact .inl (.inr hX)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
