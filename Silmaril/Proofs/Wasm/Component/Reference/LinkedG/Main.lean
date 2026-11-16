module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Basic

/-!
# Linking with an abstract exporter: specification and IR, both ways

The proofs of `Linked2.sessToIR` (`LinkedSessionIR.Rounds`) and `Linked2.irToSpec`
(`LinkedSessionAdeq.Linked`) with the exporter's facts taken from `ExpSpec.Adeq` instead of
#676's lemmas about `Simple`:

* the layers of `linkComp` (`expNodeG`, `impNodeG`, `envG`, `denU_toCompG`, the wiring);
* forward: `expEnvG` (an `ExpRun` of the exporter is a play of the first environment, by
  `ExpSpec.Adeq.fwd`), `link_layersG`, `sessToIRU` (session rounds are complete rounds of
  `g.toComp.denU`), `sess_specToIR` (`SessSpec` sessions are plays of `g.toComp.den`);
* backward: `expEnvG_inv` (complete rounds of the first environment are plays of the
  exporter's IR, which then are sessions by `ExpSpec.Adeq.bwd`), `readbackU` (complete rounds
  of typed calls of `g.toComp.denU` are session rounds), `irToSpec`;
* `toExp_adeq`: a linked component meets `ExpSpec.Adeq`; `chain_adeq`: so does every chain.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedG

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The layers of the linked component -/

/-- The node of the exporter. -/
abbrev expNodeG (C : CoreSem ImpModule) (g : LinkedG) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH 0 [])).comp (g.exp.comp.denU C)

/-- The wiring of the importer's imports to the exporter's exports. -/
abbrev wireArgsG (g : LinkedG) : List Impl := g.wire.map fun w => ⟨[], .call w⟩

/-- The node of the importer. -/
abbrev impNodeG (C : CoreSem ImpModule) (g : LinkedG) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH g.exp.comp.exports.length (wireArgsG g))).comp
    (g.imp.toComp.denU C)

/-- The environment of the linked component's exports: the exporter, then the importer. -/
abbrev envG (C : CoreSem ImpModule) (g : LinkedG) : Strategy sigU sigU :=
  ext g.exp.comp.exports.length (ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG C g))
    (impNodeG C g)

theorem denU_toCompG (C : CoreSem ImpModule) (g : LinkedG) :
    g.toComp.denU C = (envG C g).comp (Strategy.ofHandler
      (exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports)) := by
  simp only [LinkedG.toComp, linkComp, Comp.denU, denNodes, Node.den, envAfter, Node.width,
    Comp.exports_mk, List.length_nil, Nat.zero_add, SimpleI.exports_length_toComp]

theorem exportsH_toCompG (g : LinkedG) {j : Nat} (hj : j < g.imp.exports.length) (p : Payload) :
    exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports (j, p) =
      .call (g.exp.comp.exports.length + j, p) fun n => .pure n := by
  have hget : (g.toComp.exports.map Export.impl)[j]? =
      some ⟨[], .call (g.exp.comp.exports.length + j)⟩ := by
    simp [LinkedG.toComp, linkComp, hj]
  simp only [exportsH, implsH, hget, Impl.prog, runChain, Target.prog,
    ite_eq_left (Nat.add_lt_add_left hj _)]

theorem implsH_wireG {g : LinkedG} {k : Nat} {w : Fin g.exp.comp.exports.length}
    (hw : g.wire[k]? = some w.val) (p : Payload) :
    implsH g.exp.comp.exports.length (wireArgsG g) (k, p) = .call (w.val, p) fun n => .pure n := by
  have hget : (wireArgsG g)[k]? = some ⟨[], .call w.val⟩ := by
    simp [wireArgsG, hw]
  simp only [implsH, hget, Impl.prog, runChain, Target.prog, ite_eq_left w.isLt]

/-- An import call of the importer, renamed to the wired export of the exporter. -/
def wireRoundG (g : LinkedG) (d : Round (sigN g.imp.imports.length)) : Round sigU :=
  ⟨(g.wire.getD d.1.1.val 0, d.1.2), d.2⟩

theorem wire_getDG {g : LinkedG} {k w : Nat} (hw : g.wire[k]? = some w) : g.wire.getD k 0 = w := by
  simp [List.getD_eq_getElem?_getD, hw]

theorem hrounds_wireG {g : LinkedG} :
    ∀ {ds : List (Round (sigN g.imp.imports.length))},
      (∀ d ∈ ds, ∃ w : Fin g.exp.comp.exports.length, g.wire[d.1.1.val]? = some w.val) →
      HRounds (implsH g.exp.comp.exports.length (wireArgsG g)) (ds.map Round.forget)
        (ds.map (wireRoundG g))
  | [], _ => .nil
  | ⟨(k, p), R⟩ :: ds, H => by
    obtain ⟨w, hw⟩ := H _ List.mem_cons_self
    have e : wireRoundG g ⟨(k, p), R⟩ = ⟨(w.val, p), R⟩ := by
      simp only [wireRoundG, wire_getDG hw]
    rw [List.map_cons, List.map_cons, e]
    exact .call (h := implsH _ _) (q := (k.val, p)) (q' := (w.val, p)) (k := fun n => .pure n)
      (implsH_wireG hw _) rfl (hrounds_wireG fun d hd => H d (List.mem_cons_of_mem _ hd))

/-! ## The exporter, forward -/

section Fwd

variable {P : Profile} {g : LinkedG}

theorem expRunG_wire : ∀ {s s' : g.exp.St} {ds : List (Round (sigN g.imp.imports.length))},
    LinkedG.ExpRun P g s ds s' →
    ∀ d ∈ ds, ∃ w : Fin g.exp.comp.exports.length, g.wire[d.1.1.val]? = some w.val
  | _, _, _, .nil _, _, hd => nomatch hd
  | _, _, _, .step w hw _ h, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨w, hw⟩
    · exact expRunG_wire h d hd

theorem expRunG_run : ∀ {s s' : g.exp.St} {ds : List (Round (sigN g.imp.imports.length))},
    LinkedG.ExpRun P g s ds s' → g.exp.Run P s (ds.map (wireRoundG g)) s'
  | _, _, _, .nil s => .nil s
  | _, _, _, .step (k := k) (p := p) (R := R) w hw hs h => by
    have e : wireRoundG g ⟨(k, p), R⟩ = ⟨(w.val, p), R⟩ := by
      simp only [wireRoundG, wire_getDG hw]
    rw [List.map_cons, e]
    exact .cons hs (expRunG_run h)

theorem expRunG_append {s s₁ s₂ : g.exp.St}
    {ds ds' : List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload)}
    (h : LinkedG.ExpRun P g s ds s₁) (h' : LinkedG.ExpRun P g s₁ ds' s₂) :
    LinkedG.ExpRun P g s (ds ++ ds') s₂ := by
  induction h with
  | nil => exact h'
  | step w hw hs _ ih => exact .step w hw hs (ih h')

theorem expRunG_split : ∀ {s s' : g.exp.St}
    (ds ds' : List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload)),
    LinkedG.ExpRun P g s (ds ++ ds') s' →
    ∃ s₁, LinkedG.ExpRun P g s ds s₁ ∧ LinkedG.ExpRun P g s₁ ds' s'
  | s, _, [], _, h => ⟨s, .nil s, h⟩
  | _, _, _ :: ds, ds', h => by
    rw [List.cons_append] at h
    cases h with
    | step w hw hs h' =>
      obtain ⟨s₁, h₁, h₂⟩ := expRunG_split ds ds' h'
      exact ⟨s₁, .step w hw hs h₁, h₂⟩

/-- **The exporter's answers in the first environment**: an `ExpRun` from the exporter's
initial state, renamed to the wired exports, is a play of the first environment. -/
theorem expEnvG (he : g.exp.Adeq P) {ds : List (Round (sigN g.imp.imports.length))}
    {s' : g.exp.St} (h : LinkedG.ExpRun P g g.exp.init ds s') :
    twos (ds.map (wireRoundG g)) ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g) := by
  have hU := he.fwd _ _ (expRunG_run h)
  rw [uMoves_eq] at hU
  have hN : twos (ds.map (wireRoundG g)) ∈ expNodeG (impSem P) g := twos_comp_upper hU
  have hP : twos ((ds.map (wireRoundG g)).map (Round.inr (F₁ := sigU))) ∈
      (Strategy.id sigU).pair (expNodeG (impSem P) g) := twos_pair_inr hN
  unfold ext
  exact twos_comp_upper (twos_comp_ofHandler (hrounds_splitH _) hP)

/-- The importer round with its import calls renamed to the wired exports. -/
def wiredG {Ii : SInst} (d : LayerI g.imp Ii) : CRound sigU sigU :=
  ⟨(g.exp.comp.exports.length + d.j.val, .vals d.vs), d.dss.flatten.map (wireRoundG g), d.ans⟩

theorem flatMap_wiredG {Ii : SInst} (L : List (LayerI g.imp Ii)) :
    (L.map (wiredG (g := g))).flatMap (·.cs) =
      (L.flatMap fun d => d.dss.flatten).map (wireRoundG g) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, List.map_append]
    rfl

/-- The importer's export layer at the untyped interface, round by round (`layers_denU`). -/
theorem layers_denUI {c : SimpleI} {Ii : SInst} (hI : c.mod.IsInst Ii) {L : List (LayerI c Ii)}
    (hL : ∀ d ∈ L, d.Ok hI) (h : cplay (L.map LayerI.l₅) ∈ envSI (impSem P) c) :
    cplay (L.map LayerI.l₆) ∈ c.toComp.denU (impSem P) := by
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (HC.of_map _ _ L fun d hd => ?_) h
  have hl' : checkLower c.exports[d.j.val].ty.params d.vs = some d.xs := (hL d hd).lower
  refine .call (h := exportsH _ _) (q' := (c.exports[d.j].core + c.imports.length, .flat d.xs))
    (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[d.j].ty)))) ?_ rfl .nil
  rw [exportsH_toCompI c d.j.isLt d.vs d.hk, hl']
  rfl

/-- **Linked calls, one after another** (`link_layersT` with an abstract exporter). -/
theorem link_layersG (he : g.exp.Adeq P) {Ii : SInst} {L : List (LayerI g.imp Ii)}
    {s' : g.exp.St} (himp : cplay (L.map LayerI.l₆) ∈ g.imp.toComp.denU (impSem P))
    (hrun : LinkedG.ExpRun P g g.exp.init (L.flatMap fun d => d.dss.flatten) s') :
    cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ : CRound sigU sigU)) ∈
      g.toComp.denU (impSem P) := by
  have hexp := expEnvG he hrun
  have hwire := expRunG_wire hrun
  have hN : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), d.dss.flatten.map (wireRoundG g),
      d.ans⟩ : CRound sigU sigU)) ∈ impNodeG (impSem P) g :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hrounds_wireG fun x hx =>
      hwire x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)) .nil) himp
  have hP : cplay (L.map fun d => (⟨.inr (d.j.val, .vals d.vs), d.dss.flatten.map (wireRoundG g),
      d.ans⟩ : CRound sigU (sigU ⊕ₛ sigU))) ∈ (Strategy.id sigU).pair (impNodeG (impSem P) g) :=
    by have h := cplay_pair_inr (σ₁ := Strategy.id sigU) hN; rwa [List.map_map] at h
  have hS : cplay (L.map (wiredG (g := g))) ∈ ((Strategy.id sigU).pair (impNodeG (impSem P) g)).comp
      (Strategy.ofHandler (splitH g.exp.comp.exports.length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay ((L.map (wiredG (g := g))).map (CRound.hide (E := sigU))) ∈ envG (impSem P) g := by
    refine cplay_comp_serve ?_ hS
    rw [flatMap_wiredG]
    exact hexp
  have hE' : cplay (L.map fun d => (⟨(g.exp.comp.exports.length + d.j.val, .vals d.vs), [], d.ans⟩ :
      CRound sigU sigU)) ∈ envG (impSem P) g := by rwa [List.map_map] at hE
  rw [denU_toCompG]
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
    .call (h := exportsH _ _) (q := (d.j.val, .vals d.vs))
      (q' := (g.exp.comp.exports.length + d.j.val, .vals d.vs)) (k := fun n => .pure n)
      (exportsH_toCompG g d.j.isLt _) rfl .nil) hE'

/-! ### The header form -/

/-- The instance round of a session round. -/
def rG {Ii : SInst} (d : LinkedG.SessRound g Ii) : CRound Ii.E Ii.F := ⟨d.f, d.cs, d.w⟩

/-- The IR round of the importer of a session round. -/
def uG {Ii : SInst} (d : LinkedG.SessRound g Ii) :
    CRound (sigN g.imp.imports.length) (sigN g.imp.toComp.exports.length) :=
  ⟨(⟨d.j, by simp [SimpleI.toComp]⟩, .vals d.vs), d.dss.flatten, d.ans⟩

/-- An IR round of the importer, its lower calls hidden, at the untyped interface. -/
def hideU (u : CRound (sigN g.imp.imports.length) (sigN g.imp.toComp.exports.length)) :
    CRound sigU sigU :=
  ⟨(u.q.1.val, u.q.2), [], u.a⟩

theorem cplay_rG {Ii : SInst} : ∀ L : List (LinkedG.SessRound g Ii),
    cplay (L.map rG) = L.flatMap LinkedG.SessRound.instMoves
  | [] => rfl
  | d :: L => by
    rw [List.map_cons, List.flatMap_cons, ← cplay_rG L]
    simp only [cplay, rG, LinkedG.SessRound.instMoves, List.cons_append,
      List.append_assoc, List.nil_append]

theorem rel_uG {Ii : SInst} : ∀ {L : List (LinkedG.SessRound g Ii)}, (∀ d ∈ L, d.Ok) →
    List.Forall₂ (fun r u => ∃ j vs, IRRoundI g.imp Ii j vs r u) (L.map rG) (L.map uG)
  | [], _ => .nil
  | d :: L, h => by
    obtain ⟨xs, hl, h₁, h₂, hrel⟩ := h d List.mem_cons_self
    exact .cons ⟨d.j, d.vs, xs, d.dss, hl, h₁, h₂, hrel, rfl⟩
      (rel_uG fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))

theorem cplay_hide {E F : Sig.{0}} : ∀ L : List (Round F),
    cplay (L.map fun r => (⟨r.1, [], r.2⟩ : CRound E F)) = twos L
  | [] => rfl
  | ⟨_, _⟩ :: L => by
    rw [List.map_cons, twos_cons, ← cplay_hide L]
    rfl

/-- **Session rounds are complete rounds of the linked IR** at the untyped interface. -/
theorem sessToIRU (he : g.exp.Adeq P) (hi : g.imp.Good) {Ii : SInst} (hIi : g.imp.mod.IsInst Ii)
    (L : List (LinkedG.SessRound g Ii)) (hL : ∀ d ∈ L, d.Ok) {q : Ii.HState}
    (hpath : Ii.Path P (.idle Ii.store) (L.flatMap LinkedG.SessRound.instMoves) q)
    {s' : g.exp.St}
    (hrun : LinkedG.ExpRun P g g.exp.init (L.flatMap fun d => d.dss.flatten) s') :
    twos (L.map LinkedG.SessRound.toU) ∈ g.toComp.denU (impSem P) := by
  rw [← cplay_rG] at hpath
  obtain ⟨La, hLa, hr, hu⟩ := layers_of hi hIi (rel_uG hL)
  have h := cplay_mem_strategy hpath
  rw [← hr] at h
  have himp := layers_denUI hIi hLa (layers_env hIi hLa (layers_sem hIi hLa h))
  have hfl : (La.flatMap fun d => d.dss.flatten) = L.flatMap fun d => d.dss.flatten := by
    have e₁ : (La.map LayerI.u).flatMap (·.cs) = La.flatMap fun d => d.dss.flatten := by
      rw [List.flatMap_map]
      rfl
    have e₂ : (L.map uG).flatMap (·.cs) = L.flatMap fun d => d.dss.flatten := by
      rw [List.flatMap_map]
      rfl
    rw [← e₁, ← e₂, hu]
  rw [← hfl] at hrun
  have hU := link_layersG he himp hrun
  have e : (La.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ : CRound sigU sigU)) =
      (L.map LinkedG.SessRound.toU).map fun r => (⟨r.1, [], r.2⟩ : CRound sigU sigU) := by
    have e₁ : (La.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ : CRound sigU sigU)) =
        (La.map LayerI.u).map (hideU (g := g)) := by
      rw [List.map_map]
      rfl
    rw [e₁, hu, List.map_map, List.map_map]
    rfl
  rw [e, cplay_hide] at hU
  exact hU

/-- A specification session is a list of session rounds. -/
theorem sessSpec_roundsG {Ii : SInst} {u u' : Store Nat} {π π' : g.exp.St}
    {calls : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (h : g.SessSpec P Ii u π calls outs u' π') :
    ∃ L : List (LinkedG.SessRound g Ii), (∀ d ∈ L, d.Ok) ∧
      Ii.Path P (.idle u) (L.flatMap LinkedG.SessRound.instMoves) (.idle u') ∧
      LinkedG.ExpRun P g π (L.flatMap fun d => d.dss.flatten) π' ∧
      L.map LinkedG.SessRound.toU =
        (calls.zip outs).map fun co => ⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩ := by
  induction h with
  | nil u π => exact ⟨[], (fun _ h => nomatch h), .nil _, .nil _, rfl⟩
  | round d hok hpath hrun hans _ ih =>
    obtain ⟨L, hL, hp, hr, hm⟩ := ih
    refine ⟨d :: L, ?_, ?_, ?_, ?_⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | h
      · exact hok
      · exact hL d' h
    · rw [List.flatMap_cons]
      exact path_append hpath hp
    · rw [List.flatMap_cons]
      exact expRunG_append hrun hr
    · rw [List.map_cons, hm, List.zip_cons_cons, List.map_cons]
      simp only [LinkedG.SessRound.toU, hans]

theorem sessSpec_lengthG {Ii : SInst} {u u' : Store Nat} {π π' : g.exp.St}
    {calls : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (h : g.SessSpec P Ii u π calls outs u' π') : calls.length = outs.length := by
  induction h with
  | nil => rfl
  | round _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

/-- The rounds of a session play, at the linked component's interface. -/
def topRoundsG (g : LinkedG) :
    List (Fin g.imp.exports.length × List IVal) → List (Option (List IVal)) →
    List (Round (sigN g.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    ⟨(⟨j, by simp [LinkedG.exports_length_toComp]⟩, .vals vs), o.map .vals⟩ :: topRoundsG g cs os
  | _, _ => []

theorem sessMoves_eqG (g : LinkedG) :
    ∀ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      g.sessMoves calls outs = twos (topRoundsG g calls outs)
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    show _ :: _ :: g.sessMoves cs os = _ :: _ :: twos (topRoundsG g cs os)
    rw [sessMoves_eqG g cs os]

theorem topRoundsG_forget (g : LinkedG) :
    ∀ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      (topRoundsG g calls outs).map Round.forget =
        (calls.zip outs).map fun co => ⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    rw [List.zip_cons_cons, List.map_cons, ← topRoundsG_forget g cs os]
    rfl

/-- **Specification sessions are IR plays.** -/
theorem sess_specToIR (he : g.exp.Adeq P) (hi : g.imp.Good) {Ii : SInst}
    (hIi : g.imp.mod.IsInst Ii) {calls : List (Fin g.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {u' : Store Nat} {π' : g.exp.St}
    (h : g.SessSpec P Ii Ii.store g.exp.init calls outs u' π') :
    g.sessMoves calls outs ∈ g.toComp.den (impSem P) := by
  obtain ⟨L, hL, hp, hr, hm⟩ := sessSpec_roundsG h
  rw [sessMoves_eqG, den_iff _ rfl, topRoundsG_forget, ← hm]
  exact sessToIRU he hi hIi L hL hp hr

end Fwd

/-! ## The read-back -/

section Back

variable {P : Profile} {g : LinkedG}

/-- A typed export call of the linked component. -/
def TopG (g : LinkedG) (m : URound) : Prop :=
  ∃ (j : Fin g.imp.exports.length) (vs : List IVal), m.1 = (j.val, .vals vs) ∧
    ValTy.checkList g.imp.exports[j].ty.params vs = true

/-- A linked call as a question of the linked environment, with its answer. -/
def shiftG (g : LinkedG) (m : URound) : Round sigU :=
  ⟨(g.exp.comp.exports.length + m.1.1, m.1.2), m.2⟩

theorem hrounds_exportsG_inv (g : LinkedG) :
    ∀ (M : List URound) (low : List (Round sigU)), (∀ m ∈ M, m.1.1 < g.imp.exports.length) →
      HRounds (exportsH (g.exp.comp.exports.length + g.imp.exports.length) g.toComp.exports)
        M low →
      low = M.map (shiftG g)
  | [], _, _, H => by cases H; rfl
  | ⟨(j, p), R⟩ :: M, low, hlt, H => by
    have hj : j < g.imp.exports.length := hlt _ List.mem_cons_self
    rcases hrounds_cons_inv H with ⟨hq, -⟩ | ⟨q', k, a', low', rfl, hq, hk, H''⟩
    · rw [exportsH_toCompG g hj] at hq
      cases hq
    · rw [exportsH_toCompG g hj] at hq
      cases hq
      cases hk
      rw [hrounds_exportsG_inv g M low' (fun m hm => hlt m (List.mem_cons_of_mem _ hm)) H'']
      rfl

/-- **The exporter's environment read back**: complete rounds of the first environment are
complete rounds of the exporter's IR. -/
theorem expEnvG_inv (he : g.exp.Adeq P) {L : List (Round sigU)}
    (h : twos L ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g)) :
    twos L ∈ g.exp.comp.denU (impSem P) := by
  have hN : ∀ t ∈ expNodeG (impSem P) g, NoInl t :=
    noInl_comp (noInl_ofHandler_pure fun _ => ⟨none, rfl⟩)
  have hX : ∀ t ∈ ((Strategy.id sigU).pair (expNodeG (impSem P) g)).comp
      (Strategy.ofHandler (splitH 0)), NoInl t :=
    noInl_pair_comp (oneShot_splitH 0) (fun q f k hq => by
      simp only [splitH, Nat.not_lt_zero, ↓reduceIte] at hq
      cases hq
      exact ⟨_, rfl⟩) hN
  unfold ext at h
  have hl₃ := twos_of_comp_noInl hX h
  have hpair : ∀ s ∈ (Strategy.id sigU).pair (expNodeG (impSem P) g),
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
  exact twos_of_comp_noInl (noInl_denU _ he.imports) hl₄

/-- A component import call wired to an export of the exporter, on values of its type. -/
def WTG (g : LinkedG) (y : Round (sigN g.imp.imports.length)) : Prop :=
  ∃ (w : Fin g.exp.comp.exports.length) (ws : List IVal), g.wire[y.1.1.val]? = some w.val ∧
    y.1.2 = .vals ws ∧ ValTy.checkList g.exp.comp.exports[w].ty.params ws = true

theorem wiredG_of (hw : g.WireTy) {k : Nat} (hk : k < g.imp.imports.length) :
    ∃ w : Fin g.exp.comp.exports.length, g.wire[k]? = some w.val ∧
      (g.imp.imports[k]?).map (fun p : String × FuncTy => p.2) = some g.exp.comp.exports[w].ty := by
  have hk' : k < g.wire.length := by
    rw [hw.length]
    exact hk
  obtain ⟨x, hx, hty⟩ := hw.ty k g.wire[k] (List.getElem?_eq_getElem hk')
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hx
  exact ⟨⟨_, hlt⟩, List.getElem?_eq_getElem hk',
    hty.trans (congrArg (fun y : Export => some y.ty) hget.symm)⟩

theorem wtG_of (hw : g.WireTy) {y : Round (sigN g.imp.imports.length)}
    {nm : String} {ft : FuncTy} {ws : List IVal}
    (hft : g.imp.imports[y.1.1.val]? = some (nm, ft)) (hy : y.1.2 = .vals ws)
    (hck : ValTy.checkList ft.params ws = true) : WTG g y := by
  obtain ⟨w, hwk, hty⟩ := wiredG_of hw y.1.1.isLt
  rw [hft] at hty
  have hft' : ft = g.exp.comp.exports[w].ty := by simpa using hty
  exact ⟨w, ws, hwk, hy, hft' ▸ hck⟩

theorem hrounds_wire_invG (hw : g.WireTy) :
    ∀ (ds : List (Round (sigN g.imp.imports.length))) (cs' : List (Round sigU)),
      HRounds (implsH g.exp.comp.exports.length (wireArgsG g)) (ds.map Round.forget) cs' →
      cs' = ds.map (wireRoundG g)
  | [], _, H => by cases H; rfl
  | ⟨(k, p), R⟩ :: ds, cs', H => by
    obtain ⟨w, hwk, -⟩ := wiredG_of hw k.isLt
    have H' : HRounds (implsH g.exp.comp.exports.length (wireArgsG g))
        (⟨(k.val, p), R⟩ :: ds.map Round.forget) cs' := H
    rcases hrounds_cons_inv H' with ⟨hq, -⟩ | ⟨q', k', a', low', rfl, hq, hk, H''⟩
    · rw [implsH_wireG hwk] at hq
      cases hq
    · rw [implsH_wireG hwk] at hq
      cases hq
      cases hk
      rw [hrounds_wire_invG hw ds low' H'']
      simp only [List.map_cons, wireRoundG, wire_getDG hwk]

/-- **A session of the exporter on typed wired calls is an `ExpRun`.** -/
theorem expRun_of_run : ∀ {s s' : g.exp.St} (ds : List (Round (sigN g.imp.imports.length))),
    (∀ d ∈ ds, WTG g d) → g.exp.Run P s (ds.map (wireRoundG g)) s' → LinkedG.ExpRun P g s ds s'
  | s, _, [], _, h => by
    cases h
    exact .nil s
  | _, _, ⟨(k, p), R⟩ :: ds, hwt, h => by
    obtain ⟨w, ws, hw, -, -⟩ := hwt _ List.mem_cons_self
    have e : wireRoundG g ⟨(k, p), R⟩ = ⟨(w.val, p), R⟩ := by
      simp only [wireRoundG, wire_getDG hw]
    rw [List.map_cons, e] at h
    cases h with
    | cons hs h' =>
      exact .step w hw hs (expRun_of_run ds (fun d hd => hwt d (List.mem_cons_of_mem _ hd)) h')

theorem round_ofG (hw : g.WireTy) {Ii : SInst} {r : CRound Ii.E Ii.F} {c : CRound sigU sigU}
    {m : URound}
    (h : ∃ x, RdI g.imp Ii r x ∧
      HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x (downBy g.exp.comp.exports.length c))
    (hc : CRound.toRound c = shiftG g m) :
    ∃ d : LinkedG.SessRound g Ii, d.Ok ∧ rG d = r ∧
      c.cs = d.dss.flatten.map (wireRoundG g) ∧ d.toU = m ∧ ∀ y ∈ d.dss.flatten, WTG g y := by
  obtain ⟨cq, ccs, ca⟩ := c
  obtain ⟨⟨j₀, p₀⟩, R⟩ := m
  obtain ⟨rq, rcs, ra⟩ := r
  have hcq : cq = (g.exp.comp.exports.length + j₀, p₀) := congrArg Sigma.fst hc
  subst hcq
  have hca : ca = R := eq_of_heq (Sigma.mk.inj hc).2
  subst hca
  obtain ⟨x, hRd, q, a, cs, cs', rfl, hy, H⟩ := h
  cases hy
  obtain ⟨j, vs, xs, dss, hxq, hcl, h₁, h₂, hF, hxcs, hxa⟩ := hRd
  have hxq' : ((g.exp.comp.exports.length + j₀ - g.exp.comp.exports.length, p₀) :
      Nat × Payload) = (j.val, .vals vs) := hxq
  rw [Nat.add_sub_cancel_left] at hxq'
  simp only [Prod.mk.injEq] at hxq'
  obtain ⟨rfl, rfl⟩ := hxq'
  have hxcs' : cs = dss.flatten.map Round.forget := hxcs
  subst hxcs'
  have hcs := hrounds_wire_invG hw dss.flatten ccs H
  refine ⟨⟨j, vs, rq, rcs, ra, dss⟩, ⟨xs, hcl, h₁, h₂, hF⟩, rfl, hcs, ?_, ?_⟩
  · have hxa' : ca = (answerPayload ra).bind (Adapter.up (.lift g.imp.exports[j].ty)) := hxa
    rw [hxa']
    rfl
  · intro y hy
    obtain ⟨ds, hds, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨x', hx'⟩ := forall₂_mem_right hF ds hds
    obtain ⟨nm, ft, ws, hft, hp, hck⟩ := impRel_typed hx' y hy
    exact wtG_of hw hft hp hck

theorem build_roundsG (hw : g.WireTy) {Ii : SInst} :
    ∀ {ri : List (CRound Ii.E Ii.F)} {cl : List (CRound sigU sigU)} {M : List URound},
      List.Forall₂ (fun r c => ∃ x, RdI g.imp Ii r x ∧
        HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
          (downBy g.exp.comp.exports.length c)) ri cl →
      List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M →
      ∃ ds : List (LinkedG.SessRound g Ii), (∀ d ∈ ds, d.Ok) ∧ ds.map rG = ri ∧
        cl.flatMap (·.cs) = (ds.flatMap fun d => d.dss.flatten).map (wireRoundG g) ∧
        ds.map LinkedG.SessRound.toU = M ∧ ∀ y ∈ ds.flatMap (fun d => d.dss.flatten), WTG g y
  | _, _, _, .nil, .nil => ⟨[], fun _ h => (nomatch h), rfl, rfl, rfl, fun _ h => (nomatch h)⟩
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    obtain ⟨d, hOk, hr, hcs, hm, hwt⟩ := round_ofG hw h₁ h₂
    obtain ⟨ds, hOks, hrs, hcss, hms, hwts⟩ := build_roundsG hw t₁ t₂
    refine ⟨d :: ds, ?_, by rw [List.map_cons, hr, hrs], ?_, by rw [List.map_cons, hm, hms], ?_⟩
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

/-- **The read-back of the linked IR**: complete rounds of typed calls of `g.toComp.denU` are
session rounds: a play of the importer's instance from its store and an `ExpRun` of the
exporter from its initial state. -/
theorem readbackU (he : g.exp.Adeq P) (hi : g.imp.Good) {Ii : SInst}
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {M : List URound} (hM : ∀ m ∈ M, TopG g m)
    (h : twos M ∈ g.toComp.denU (impSem P)) :
    ∃ ds : List (LinkedG.SessRound g Ii), (∀ d ∈ ds, d.Ok) ∧
      ds.map LinkedG.SessRound.toU = M ∧
      (∃ q, Ii.Path P (.idle Ii.store) (ds.flatMap LinkedG.SessRound.instMoves) q) ∧
      ∃ s', LinkedG.ExpRun P g g.exp.init (ds.flatMap fun d => d.dss.flatten) s' := by
  have hEnv : ∀ t ∈ envG (impSem P) g, NoInl t :=
    noInl_comp (noInl_comp (noInl_ofHandler_pure pure_maskH0))
  rw [denU_toCompG] at h
  obtain ⟨l₂, H₂, hl₂⟩ := hrounds_of_comp (oneShot_implsH _ _) hEnv h
  rw [hrounds_exportsG_inv g M l₂ (fun m hm => by
    obtain ⟨j, vs, hq, -⟩ := hM m hm
    rw [hq]
    exact j.isLt) H₂] at hl₂
  have hσ : ∀ s ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNodeG (impSem P) g), NoInl s :=
    noInl_comp (noInl_ofHandler_pure pure_maskH0)
  obtain ⟨cl, hcl, hA, hmap⟩ := serve_inv hσ hl₂
  have K : List.Forall₂ (fun c m => CRound.toRound c = shiftG g m) cl M :=
    forall₂_of_map_eq hmap
  obtain ⟨low₁, H₁, hlow₁⟩ := hc_inv (oneShot_splitH _) hcl
  have hge : ∀ r ∈ cl, g.exp.comp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨m, hm⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (g.exp.comp.exports.length + m.1.1, m.1.2) := congrArg Sigma.fst hm
    rw [h₁]
    exact Nat.le_add_right _ _
  rw [hc_splitH_inv H₁ hge] at hlow₁
  have hN := cplay_of_pair_inr hlow₁
  obtain ⟨up₂, H₂', hup₂⟩ := hb_inv (oneShot_implsH _ _) hN
  have G₂ : List.Forall₂ (fun x c => HBR (implsH g.exp.comp.exports.length (wireArgsG g)) x
      (downBy g.exp.comp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂')
  have htop : ∀ x ∈ up₂, TopI g.imp x := by
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
  obtain ⟨ri, hri, F⟩ := imp_readback hi hIi htop hup₂
  obtain ⟨ds, hOk, hr, hcs, hm, hWT⟩ := build_roundsG hw (forall₂_comp F G₂) K
  rw [hcs] at hA
  have hU := expEnvG_inv he hA
  have hTy : ∀ r ∈ (ds.flatMap fun d => d.dss.flatten).map (wireRoundG g), g.exp.Typed r := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    obtain ⟨w, ws, hwy, hp, hck⟩ := hWT y hy
    refine ⟨w, ws, ?_, hck⟩
    show (g.wire.getD y.1.1.val 0, y.1.2) = _
    rw [wire_getDG hwy, hp]
  obtain ⟨s', hS⟩ := he.bwd _ hTy (by rw [uMoves_eq]; exact hU)
  have hrun := expRun_of_run _ hWT hS
  obtain ⟨q, hq⟩ := Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff.mp hri
  rw [← hr, cplay_rG] at hq
  exact ⟨ds, hOk, hm, ⟨q, hq⟩, s', hrun⟩

/-- **Session rounds read back are a specification session.** -/
theorem sessSpec_ofG {Ii : SInst} :
    ∀ (ds : List (LinkedG.SessRound g Ii)) (calls : List (Fin g.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) {u : Store Nat} {π π' : g.exp.St} {q : Ii.HState},
      ds.map LinkedG.SessRound.toU =
        (calls.zip outs).map (fun co => ⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩) →
      calls.length = outs.length → (∀ d ∈ ds, d.Ok) →
      Ii.Path P (.idle u) (ds.flatMap LinkedG.SessRound.instMoves) q →
      LinkedG.ExpRun P g π (ds.flatMap fun d => d.dss.flatten) π' →
      ∃ u', g.SessSpec P Ii u π calls outs u' π'
  | [], calls, outs, u, π, π', q, hF, hlen, _, _, hrun => by
    cases hrun
    have hz : calls.zip outs = [] := List.map_eq_nil_iff.mp hF.symm
    rcases List.zip_eq_nil_iff.mp hz with rfl | rfl
    · have : outs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst this
      exact ⟨u, .nil u π⟩
    · have : calls = [] := List.length_eq_zero_iff.mp hlen
      subst this
      exact ⟨u, .nil u π⟩
  | d :: ds, calls, outs, u, π, π', q, hF, hlen, hOk, hp, hrun => by
    rcases calls with _ | ⟨⟨j, vs⟩, cs⟩
    · cases hF
    rcases outs with _ | ⟨o, os⟩
    · cases hF
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.cons.injEq] at hF
    obtain ⟨hd, hF'⟩ := hF
    have hq : (d.j.val, Payload.vals d.vs) = (j.val, Payload.vals vs) := congrArg Sigma.fst hd
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hq
    obtain ⟨hj, hvs⟩ := hq
    have hans : d.ans = o.map .vals := eq_of_heq (Sigma.mk.inj hd).2
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunG_split _ _ hrun
    obtain ⟨u', hS⟩ := sessSpec_ofG ds cs os hF' (by simpa using hlen)
      (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂
    have hjv : (d.j, d.vs) = (j, vs) := by rw [Fin.ext hj, hvs]
    rw [← hjv]
    exact ⟨u', .round d (hOk d List.mem_cons_self) hp₁ hr₁ hans hS⟩

/-- **IR session plays of typed calls are specification sessions.** -/
theorem irToSpec (he : g.exp.Adeq P) (hi : g.imp.Good) {Ii : SInst}
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy)
    (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls g.imp calls) (hlen : calls.length = outs.length)
    (h : g.sessMoves calls outs ∈ g.toComp.den (impSem P)) :
    ∃ (u' : Store Nat) (π' : g.exp.St), g.SessSpec P Ii Ii.store g.exp.init calls outs u' π' := by
  rw [sessMoves_eqG, den_iff _ rfl, topRoundsG_forget] at h
  have hM : ∀ m ∈ (calls.zip outs).map (fun co =>
      (⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩ : URound)), TopG g m := by
    intro m hm
    obtain ⟨co, hco, rfl⟩ := List.mem_map.mp hm
    exact ⟨co.1.1, co.1.2, rfl, ht _ (List.of_mem_zip hco).1⟩
  obtain ⟨ds, hOk, hm, ⟨q, hq⟩, s', hrun⟩ := readbackU he hi hIi hw hM h
  obtain ⟨u', hS⟩ := sessSpec_ofG ds calls outs hm hlen hOk hq hrun
  exact ⟨u', s', hS⟩

end Back

/-! ## A linked component as an exporter -/

section Exp

variable {P : Profile} {g : LinkedG} {Ii : SInst}

theorem rounds_of_run : ∀ {s s' : (g.toExp Ii).St} {L : List URound},
    (g.toExp Ii).Run P s L s' →
    ∃ ds : List (LinkedG.SessRound g Ii), (∀ d ∈ ds, d.Ok) ∧
      Ii.Path P (.idle s.1) (ds.flatMap LinkedG.SessRound.instMoves) (.idle s'.1) ∧
      LinkedG.ExpRun P g s.2 (ds.flatMap fun d => d.dss.flatten) s'.2 ∧
      ds.map LinkedG.SessRound.toU = L
  | _, _, _, .nil s => ⟨[], (fun _ h => nomatch h), .nil _, .nil _, rfl⟩
  | _, _, _, .cons ⟨d, hOk, hp, hr, hd⟩ h => by
    obtain ⟨ds, hOks, hps, hrs, hms⟩ := rounds_of_run h
    refine ⟨d :: ds, ?_, ?_, ?_, by rw [List.map_cons, hms, hd]⟩
    · intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact hOk
      · exact hOks d' hd'
    · rw [List.flatMap_cons]
      exact path_append hp hps
    · rw [List.flatMap_cons]
      exact expRunG_append hr hrs

theorem run_of_rounds : ∀ (ds : List (LinkedG.SessRound g Ii)) {u : Store Nat} {π π' : g.exp.St}
    {q : Ii.HState}, (∀ d ∈ ds, d.Ok) →
    Ii.Path P (.idle u) (ds.flatMap LinkedG.SessRound.instMoves) q →
    LinkedG.ExpRun P g π (ds.flatMap fun d => d.dss.flatten) π' →
    ∃ u', (g.toExp Ii).Run P (u, π) (ds.map LinkedG.SessRound.toU) (u', π')
  | [], u, π, π', q, _, _, hrun => by
    cases hrun
    exact ⟨u, .nil _⟩
  | d :: ds, u, π, π', q, hOk, hp, hrun => by
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunG_split _ _ hrun
    obtain ⟨u', hR⟩ := run_of_rounds ds (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd'))
      hp₂ hr₂
    exact ⟨u', .cons (s₁ := (u₁, π₁)) ⟨d, hOk d List.mem_cons_self, hp₁, hr₁, rfl⟩ hR⟩

theorem toComp_ty (g : LinkedG) {w : Nat} (h₁ : w < g.toComp.exports.length)
    (h₂ : w < g.imp.exports.length) : g.toComp.exports[w].ty = g.imp.exports[w].ty := by
  simp [LinkedG.toComp, linkComp]

/-- **A linked component meets the exporter interface.** -/
theorem toExp_adeq (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) : (g.toExp Ii).Adeq P where
  imports := rfl
  fwd L s' h := by
    obtain ⟨ds, hOk, hp, hr, rfl⟩ := rounds_of_run h
    rw [uMoves_eq]
    exact sessToIRU he hi hIi ds hOk hp hr
  bwd L ht h := by
    rw [uMoves_eq] at h
    have hM : ∀ m ∈ L, TopG g m := by
      intro m hm
      obtain ⟨w, ws, hq, hck⟩ := ht m hm
      have hw' : w.val < g.imp.exports.length := by
        exact (LinkedG.exports_length_toComp g) ▸ w.isLt
      refine ⟨⟨w.val, hw'⟩, ws, hq, ?_⟩
      have e : g.toComp.exports[w.val].ty = g.imp.exports[w.val].ty := toComp_ty g w.isLt hw'
      show ValTy.checkList g.imp.exports[w.val].ty.params ws = true
      rw [← e]
      exact hck
    obtain ⟨ds, hOk, rfl, ⟨q, hq⟩, s', hrun⟩ := readbackU he hi hIi hw hM h
    obtain ⟨u', hR⟩ := run_of_rounds ds hOk hq hrun
    exact ⟨(u', s'), hR⟩

end Exp

/-! ## Chains -/

theorem chain_adeq (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst), e.Adeq P →
      ChainOk e bs Is → (chainExp e bs Is).Adeq P
  | _, [], [], he, _ => he
  | _, (_, _) :: _, _ :: Is, he, ⟨hb, hI, hw, h⟩ => chain_adeq P _ _ Is (toExp_adeq he hb hI hw) h
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

theorem chain_comp :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst),
      ChainOk e bs Is → (chainExp e bs Is).comp = chainComp e.comp bs
  | _, [], [], _ => rfl
  | _, (_, _) :: _, _ :: Is, ⟨_, _, _, h⟩ => chain_comp _ _ Is h
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

end Silmaril.Proofs.Wasm.Component.Reference.LinkedG

/-! ## `Linked2` as an instance, on the IR side -/

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedG

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

theorem topRounds_forget (l : Linked2) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      (topRounds l calls outs).map Round.forget =
        (calls.zip outs).map fun co => ⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, o :: os => by
    rw [List.zip_cons_cons, List.map_cons, ← topRounds_forget l cs os]
    rfl

theorem sessMoves_toG_iff (P : Profile) (l : Linked2) (Ie : SInst)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))) :
    (l.toG Ie).sessMoves calls outs ∈ (l.toG Ie).toComp.den (impSem P) ↔
      l.sessMoves calls outs ∈ l.toComp.den (impSem P) := by
  rw [sessMoves_eqG, den_iff _ rfl, topRoundsG_forget, sessMoves_eq, den_iff _ rfl,
    topRounds_forget, toG_toComp]

theorem toG_wireTy {l : Linked2} (hw : l.WireTy) (Ie : SInst) : (l.toG Ie).WireTy where
  length := hw.length
  ty k w hk := by
    obtain ⟨x, hx, hty⟩ := hw.ty k w hk
    refine ⟨{ name := x.name, ty := x.ty, impl := ⟨[.lift x.ty], .call (x.core + 0)⟩ }, ?_, hty⟩
    simp [SimpleI.ofSimple, SimpleI.toComp, List.getElem?_map, hx]

/-- `Linked2.sessIR_iff`, re-derived through `Linked2.toG`. -/
theorem linked2_sessIR_iff (P : Profile) (l : Linked2) (hl : l.Adequate) {Ie Ii : SInst}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length) :
    l.sessMoves calls outs ∈ l.toComp.den (impSem P) ↔
      ∃ u' π' : Store Nat, l.SessSpec P Ie Ii Ii.store Ie.store calls outs u' π' := by
  rw [← sessMoves_toG_iff P l Ie]
  have he := simple_adeq P hl.expGood hIe
  constructor
  · intro h
    obtain ⟨u', π', hS⟩ := irToSpec (g := l.toG Ie) he hl.impGood hIi
      (toG_wireTy hl.wireTy Ie) calls outs ht hlen h
    exact ⟨u', π', sessSpec_of_toG hS⟩
  · rintro ⟨u', π', hS⟩
    exact sess_specToIR (g := l.toG Ie) he hl.impGood hIi (toG_of_sessSpec hS)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedG
