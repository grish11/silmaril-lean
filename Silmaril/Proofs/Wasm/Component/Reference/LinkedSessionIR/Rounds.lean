module

public import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkIR
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.IRSess
public import Silmaril.Proofs.Wasm.Component.Reference.Litmus

/-!
# The IR side of linked sessions: general lemmas

* `expRunT_rounds`: an `ExpRunT` (returned and trapped exporter calls, both threading the store)
  is a complete activation of the exporter's instance from store to store and rounds through
  its export handlers, renamed to the wired exports (`expRun_rounds` for `ExpRun`, with
  `trapAt_rounds` for the trapped calls);
* `link_layersT`, `linked_seq_denT`, `linked2_sessToIR`: `link_layers`, `linked_seq_den` and
  their header form with `ExpRunT` in place of `ExpRun`;
* `fill_trap_steps`, `resume_trap_reach`, `trapImport_path`: a core instance stopped at an import
  call that is answered by a trap runs, host-free and with its store unchanged, to a trap, and
  answers its export call with a trap;
* `impRel_trap`: a core import call answered by a trap corresponds (`ImpRel`) to the component
  import call answered `none`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## The exporter, traps continuing -/

/-- Every import call of an `ExpRunT` is wired to an export of the exporter. -/
theorem expRunT_wire {P : Profile} {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      Linked2.ExpRunT P l I s ds s' →
      ∀ d ∈ ds, ∃ w : Fin l.exp.exports.length, l.wire[d.1.1.val]? = some w.val
  | _, _, _, .nil _, _, hd => nomatch hd
  | _, _, _, .ret w hw _ hrun, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨w, hw⟩
    · exact expRunT_wire hrun d hd
  | _, _, _, .trap w hw _ hrun, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨w, hw⟩
    · exact expRunT_wire hrun d hd

/-- **The exporter's answers, traps continuing**: import calls answered by the exporter's
specification from a well-formed store `s` to `s'`, returned and trapped calls alike, renamed
to the wired exports, are rounds of the exporter's IR export handler, played by a complete
activation of its instance from `s` to `s'` (`expRun_rounds` for `ExpRun`). -/
theorem expRunT_rounds {P : Profile} {l : Linked2} (hc : l.exp.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : l.exp.mod.IsInst I) :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      Linked2.ExpRunT P l I s ds s' → I.WellFormed s →
      ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))),
        I.Activation P s (twos li) s' ∧ HRounds (exportH (instNum hI)) lc li ∧
        HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports) (ds.map (wireRound l))
          (lc.map Round.forget)
  | _, _, _, .nil _, _ => ⟨[], [], .nil _, .nil, .nil⟩
  | _, _, _, .ret (k := k) (ws := ws) (us := us) w hw hret hrun, hwf => by
    have hwf' : I.WellFormed _ := hret.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := retAt_rounds hc hI hwf hret
    obtain ⟨li, lc, hact, H, X⟩ := expRunT_rounds hc hI hrun hwf'
    have e : wireRound l ⟨(k, .vals ws), some (.vals us)⟩ =
        ⟨(w.val, .vals ws), some (.vals us)⟩ := by
      simp only [wireRound, wire_getD hw]
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.map_cons, e, List.map_append]
      exact X₁.append X
  | _, _, _, .trap (k := k) (ws := ws) w hw htrap hrun, hwf => by
    have hwf' : I.WellFormed _ := htrap.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨li₁, lc₁, hact₁, H₁, X₁⟩ := trapAt_rounds hc hI hwf htrap
    obtain ⟨li, lc, hact, H, X⟩ := expRunT_rounds hc hI hrun hwf'
    have e : wireRound l ⟨(k, .vals ws), none⟩ = ⟨(w.val, .vals ws), none⟩ := by
      simp only [wireRound, wire_getD hw]
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact path_append hact₁ hact
    · rw [List.map_cons, e, List.map_append]
      exact X₁.append X

/-- The exporter's activation is a play of its instance from the first store. -/
theorem expRunT_mem {P : Profile} {l : Linked2} (hc : l.exp.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : l.exp.mod.IsInst I)
    {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))}
    (hrun : Linked2.ExpRunT P l I s ds s') (hwf : I.WellFormed s) :
    ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))),
      twos li ∈ I.strategy P s ∧ HRounds (exportH (instNum hI)) lc li ∧
      HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports) (ds.map (wireRound l))
        (lc.map Round.forget) := by
  obtain ⟨li, lc, hact, H, X⟩ := expRunT_rounds hc hI hrun hwf
  refine ⟨li, lc, ?_, H, X⟩
  have h' := Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact (I.strategy P s').nil_mem
  rwa [List.append_nil] at h'

/-! ## Linked calls, traps continuing -/

section Seq

variable {P : Profile} {l : Linked2} {Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- **Linked calls, one after another, exporter traps continuing** (`link_layers` with
`ExpRunT`). -/
theorem link_layersT (hc : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) {L : List (LayerI l.imp Ii)} {s' : Store Nat}
    (himp : cplay (L.map LayerI.l₆) ∈ l.imp.toComp.denU (impSem P))
    (hrun : Linked2.ExpRunT P l Ie Ie.store (L.flatMap fun d => d.dss.flatten) s') :
    cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ : CRound sigU sigU)) ∈
      l.toComp.denU (impSem P) := by
  obtain ⟨li, lc, hli, H, X⟩ := expRunT_mem hc hIe hrun hIe.1.choose_spec.ok
  have hexp : twos ((L.flatMap fun d => d.dss.flatten).map (wireRound l)) ∈
      ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l) := expEnv_rounds hIe hli H X
  have hwire : ∀ x ∈ L.flatMap (fun d => d.dss.flatten),
      ∃ w : Fin l.exp.exports.length, l.wire[x.1.1.val]? = some w.val := expRunT_wire hrun
  have hN : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l),
      d.ans⟩ : CRound sigU sigU)) ∈ impNode (impSem P) l :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hrounds_wire fun x hx =>
      hwire x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)) .nil) himp
  have hP : cplay (L.map fun d => (⟨.inr (d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l),
      d.ans⟩ : CRound sigU (sigU ⊕ₛ sigU))) ∈ (Strategy.id sigU).pair (impNode (impSem P) l) :=
    by have h := cplay_pair_inr (σ₁ := Strategy.id sigU) hN; rwa [List.map_map] at h
  have hS : cplay (L.map LayerI.wired) ∈ ((Strategy.id sigU).pair (impNode (impSem P) l)).comp
      (Strategy.ofHandler (splitH l.exp.exports.length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay ((L.map LayerI.wired).map (CRound.hide (E := sigU))) ∈ envL (impSem P) l := by
    refine cplay_comp_serve ?_ hS
    rw [flatMap_wired]
    exact hexp
  have hE' : cplay (L.map fun d => (⟨(l.exp.exports.length + d.j.val, .vals d.vs), [], d.ans⟩ :
      CRound sigU sigU)) ∈ envL (impSem P) l := by rwa [List.map_map] at hE
  rw [denU_toCompL]
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
    .call (h := exportsH _ _) (q := (d.j.val, .vals d.vs))
      (q' := (l.exp.exports.length + d.j.val, .vals d.vs)) (k := fun n => .pure n)
      (exportsH_toCompL l d.j.isLt _) rfl .nil) hE'

end Seq

/-- **The IR side for sequences of linked calls, exporter traps continuing**
(`linked_seq_den` with `ExpRunT`). -/
theorem linked_seq_denT {P : Profile} {l : Linked2} (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {lr : List (CRound Ii.E Ii.F)}
    {lu : List (CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length))}
    (hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI l.imp Ii j vs r u) lr lu)
    (h : cplay lr ∈ Ii.strategy P Ii.store) {s' : Store Nat}
    (hrun : Linked2.ExpRunT P l Ie Ie.store (lu.flatMap (·.cs)) s') :
    cplay (lu.map (Linked2.linkRound l)) ∈ l.toComp.den (impSem P) := by
  obtain ⟨L, hL, rfl, rfl⟩ := layers_of hi hIi hrel
  have himp := layers_denU hIi hL (layers_env hIi hL (layers_sem hIi hL h))
  rw [List.flatMap_map] at hrun
  have hU := link_layersT he hIe himp hrun
  have hW : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ :
      CRound (l.toComp.imports.sig) sigU)) ∈
      (Strategy.ofHandler (widenH l.toComp.imports.length)).comp (l.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun _ _ => .cons .nil .nil) hU
  rw [List.map_map]
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun _ _ => .call (h := narrowH _) rfl rfl .nil) hW

/-! ## The header form -/

section Header

variable {l : Linked2} {Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- The instance round of a session round. -/
def SessRound.r (d : Linked2.SessRound l Ii) : CRound Ii.E Ii.F := ⟨d.f, d.cs, d.w⟩

/-- The IR round of the importer of a session round. -/
def SessRound.u (d : Linked2.SessRound l Ii) :
    CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length) :=
  ⟨(⟨d.j, by simp [SimpleI.toComp]⟩, .vals d.vs), d.dss.flatten, d.ans⟩

theorem cplay_r : ∀ L : List (Linked2.SessRound l Ii),
    cplay (L.map SessRound.r) = L.flatMap Linked2.SessRound.instMoves
  | [] => rfl
  | d :: L => by
    rw [List.map_cons, List.flatMap_cons, ← cplay_r L]
    simp only [cplay, SessRound.r, Linked2.SessRound.instMoves, List.cons_append,
      List.append_assoc, List.nil_append]

theorem cplay_link : ∀ L : List (Linked2.SessRound l Ii),
    cplay ((L.map SessRound.u).map (Linked2.linkRound l)) =
      L.flatMap Linked2.SessRound.linkMoves
  | [] => rfl
  | d :: L => by
    rw [List.map_cons, List.map_cons, List.flatMap_cons, ← cplay_link L]
    rfl

theorem flatMap_u_cs (L : List (Linked2.SessRound l Ii)) :
    (L.map SessRound.u).flatMap (·.cs) = L.flatMap fun d => d.dss.flatten := by
  rw [List.flatMap_map]
  rfl

theorem rel_u : ∀ {L : List (Linked2.SessRound l Ii)}, (∀ d ∈ L, d.Ok) →
    List.Forall₂ (fun r u => ∃ j vs, IRRoundI l.imp Ii j vs r u)
      (L.map SessRound.r) (L.map SessRound.u)
  | [], _ => .nil
  | d :: L, h => by
    obtain ⟨xs, hl, h₁, h₂, hrel⟩ := h d List.mem_cons_self
    exact .cons ⟨d.j, d.vs, xs, d.dss, hl, h₁, h₂, hrel, rfl⟩
      (rel_u fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))

end Header

/-- **The IR side of linked sessions, exporter traps continuing** (proved). -/
theorem linked2_sessToIR : Linked2.SessToIR := by
  intro P l he hi Ie hIe Ii hIi L hL q hpath s' hrun
  rw [← cplay_r] at hpath
  rw [← flatMap_u_cs] at hrun
  rw [← cplay_link]
  exact linked_seq_denT he hi hIe hIi (rel_u hL) (cplay_mem_strategy hpath) hrun

/-! ## An import call answered by a trap -/

/-- A trap in a callout context reaches the top, host-free, with the store unchanged. -/
theorem fill_trap_steps {P : Profile} (s : Store Nat) :
    ∀ (E : Ctx) (f : Frame), ∃ f', Steps P Det.noHost ⟨s, f, E.fill [.trap]⟩ ⟨s, f', [.trap]⟩ := by
  have top : ∀ (g : Frame) (pre : List Execution.Core.Val) (rest : List Admin),
      Steps P Det.noHost ⟨s, g, vals pre ++ [.trap] ++ rest⟩ ⟨s, g, [.trap]⟩ := by
    intro g pre rest
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .single (Step.trapInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals] using (Relation.ReflTransGen.refl : Steps P Det.noHost ⟨s, g, [.trap]⟩ _)
  intro E
  induction E with
  | top pre rest => intro f; exact ⟨f, top f pre rest⟩
  | label pre n cont E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest)
      (Steps.label (n := n) (cont := cont) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapLabel))).trans (top f' pre rest)⟩
  | handler pre n cs E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih f
    exact ⟨f', ((Steps.ctxtInstrs (vs := pre) (rest := rest)
      (Steps.handler (n := n) (cs := cs) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapHandler))).trans (top f' pre rest)⟩
  | frame pre n fi E rest ih =>
    intro f
    obtain ⟨f', h⟩ := ih fi
    exact ⟨f, ((Steps.ctxtInstrs (vs := pre) (rest := rest) (Steps.frame (f := f) (n := n) h)).trans
      (Steps.ctxtInstrs (Relation.ReflTransGen.single Step.trapFrame))).trans (top f pre rest)⟩

/-- **A thread at a callout resumed with a trap** runs, host-free and with its store unchanged,
to a trap. -/
theorem resume_trap_reach {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Execution.Core.Val} (hco : Silmaril.Wasm.Game.CalloutAt s t h args) :
    ∃ t', Silmaril.Wasm.Game.Reach P (s, resumeResult s t .trap) (s, t') ∧
      Silmaril.Wasm.Game.ResultAt s t' .trap := by
  obtain ⟨E, a, hd⟩ := hco
  have hres : resumeResult s t .trap = .active (t.config s).frame (E.fill [.trap]) := by
    unfold resumeResult
    simp only [hd]
    rfl
  obtain ⟨f', hst⟩ := fill_trap_steps (P := P) s E (t.config s).frame
  rw [hres]
  obtain ⟨s₁, t₁, hr, hd₁⟩ :=
    Litmus.reach_of_steps (t := .active (t.config s).frame (E.fill [.trap])) hst
  have hs : s₁ = s := by
    have h₁ : (t₁.config s₁).store = s₁ := by cases t₁ <;> rfl
    rw [← h₁, hd₁]
  subst hs
  refine ⟨t₁, hr, ?_⟩
  show (t₁.config s₁).code = _
  rw [hd₁]
  rfl

/-- **An import call answered by a trap traps the export call**: a running export call `f` of
an instance that runs host-free to an import call `e`, answered by a trap, answers `f` with a
trap, at the store the import call was made in. -/
theorem trapImport_path {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile} {q : I.HState}
    {p : List (Move I.E I.F)} {f : I.F.Op} {s s' : Store Nat} {t t' : Thread} {h : Nat}
    {args : List Execution.Core.Val} {e : I.E.Op} (hp : I.Path P q p (.running f s t))
    (run : Silmaril.Wasm.Game.Reach P (s, t) (s', t'))
    (co : Silmaril.Wasm.Game.CalloutAt s' t' h args) (op : I.importOp? h args = some e) :
    I.Path P q (p ++ [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) (.idle s') := by
  obtain ⟨t'', hr, hres⟩ := resume_trap_reach (P := P) co
  exact path_append hp (.cons (.ucall run co op) (.cons (.uret .trap)
    (.cons (.oret hr hres rfl) (.nil _))))

/-- **A core import call answered by a trap** is the component import call on the lifted
arguments answered `none`. -/
theorem impRel_trap {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance} {e : I.E.Op}
    {nm : String} {ft : FuncTy} (hk : c.imports[e.1.val]? = some (nm, ft))
    {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs ft.params (e.2.1.filterMap toFlat?) = some ws) :
    ImpRel c I ⟨e, .trap⟩ [⟨(⟨e.1.val, (List.getElem?_eq_some_iff.mp hk).1⟩, .vals ws), none⟩] := by
  refine ⟨nm, ft, none, hk, rfl, ?_⟩
  simp only [hws]
  exact ⟨(List.getElem?_eq_some_iff.mp hk).1, none, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
