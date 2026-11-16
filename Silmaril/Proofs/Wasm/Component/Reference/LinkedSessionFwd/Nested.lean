module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Core

/-!
# Forward runs of a linked call: nested calls at the core level

At a callout of the importer's part to import `k`, wired to the exporter's export `xe`:

* `LInv.resume_fwd`: a returned call of the exporter's specification (`RetAt`) from the
  exporter's store `π` to `π'` is a core run of the exporter's activation in the shared store
  returning flat values that lift to the call's results; the shared thread resumed with their
  lowering and the part resumed with the same values satisfy `LInv` at `π'` (the forward
  counterpart of `LInv.resume`);
* `LInv.expTrap_fwd`: a trapped call of the exporter's specification (`TrapAt`) from `π` to `π₂`
  is a core run of the exporter's activation in the shared store to a trap, or to flat values
  of the result types that do not lift; `LReady` holds at the shared store of that end, the
  part's store at the callout and `π₂` (the forward counterpart of `lready_expTrap`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4 Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type} {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
  {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ}
  {Op₀ Oc₀ : Own} {f : Ii.F.Op}

/-- **A returned nested call of the specification, forward**: the exporter's activation in the
shared store returns flat values lifting to `us`; resuming both threads re-establishes `LInv`
at the exporter's end store `π'`. -/
theorem LInv.resume_fwd (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k : Nat} {nm : String} {w : Nat} {xe : SimpleExport} {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val} {e : Ii.E.Op}
    (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hxe : l.exp.exports[w]? = some xe)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) {ws us : List Silmaril.Wasm.Component.Val}
    {π' : Store Nat} (hRet : RetAt P l.exp Ie xe ws π us π') :
    ∃ (ev : CoreSt (E3 P)) (zs : List Flat),
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) ev ∧
      (E3 P).status ev.1 ev.2 = .returned (.values zs) ∧ liftArgs xe.ty.results zs = some us ∧
      LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f
        (ev.1, (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)))
        (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
          (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  obtain ⟨t', cvs, zs, run, final, hm, hus⟩ := hRet.run
  obtain ⟨ev, ρp', Op', hrun, hLe, hR', hF', hfe⟩ := exp_fwd (gL P l) (gLInv P l)
    (hostsSat_lstat S hI.funcs) hR hI.fnE (S.owned xe hmem) (lowerArgs xe.ty.params ws) run
  have hst := status_of_values (gL P l) hLe final hm
  have hwf' : Ie.WellFormed π' := RetAt.wellFormed S.expInst (S.expGood.core xe hmem) hI.wf hRet
  have hfm : (Store.mapH (gL P l) ev.1).funcs = (Store.mapH (gL P l) y.1).funcs :=
    mapH_funcs_eq (gL P l) hfe
  have hL1 : LinkSt s₀ ρc Oc x (Store.mapH (gL P l) ev.1, y.2) := linkSt_transport hL hfm hR'.rc
  have hL2 : LinkSt s₀ ρc Oc
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)))
      (Store.mapH (gL P l) ev.1, Silmaril.Wasm.SingleThreaded.resumeResult
        (Store.mapH (gL P l) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) :=
    link_resume hL1 hdx (ofFlat_scalar _)
  have hres : (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH (gL P l) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values ev.1 y.2 _).trans (resumeResult_mapH (gL P l) ev.1 y.2 _).symm
  have hcheck : ValTy.checkList xe.ty.results us = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hus
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, resAnswer S hk hek.1 hcheck⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨ev, zs, hrun, hst, hus, ⟨⟨ρp', Op', ρc, Oc, hres ▸ hL2, hR'⟩, hF', hwf',
    hfe.trans hI.funcs, ?_⟩⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

/-- **A trapped nested call of the specification, forward**: the exporter's activation in the
shared store ends in a trap, or in flat values of the result types that do not lift; `LReady`
holds at its end, the part's store at the callout and the exporter's store `π₂` after the trap. -/
theorem LInv.expTrap_fwd {u : Store Nat} (S : LStat P l Ie Ii u F₀ B (ownOf s₀))
    {cs : Store (CanonHost (E3 P))} {π : Store Nat} (hR : LReady P l Ie Ii s₀ u₀ F₀ cs u π)
    {y : CoreSt (E3 P)} {x : Store Nat × STh} {π' : Store Nat}
    (hI : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π')
    {xe : SimpleExport} (hxe : xe ∈ l.exp.exports) {ws : List Silmaril.Wasm.Component.Val}
    {π₂ : Store Nat} (hT : TrapAt P l.exp Ie xe ws π' π₂) :
    ∃ e : CoreSt (E3 P),
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) e ∧
      ((E3 P).status e.1 e.2 = .returned .trap ∨
        ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
          zs.map (·.type) = ValTy.flatList xe.ty.results ∧ liftArgs xe.ty.results zs = none) ∧
      LReady P l Ie Ii s₀ u₀ F₀ e.1 x.1 π₂ := by
  have hR' := lready_after hR hI
  obtain ⟨ρp, Op, ρc, Oc, hR4⟩ := hR'.rel
  obtain ⟨t', res, run, final, hout⟩ := hT.run
  obtain ⟨e, ρp', Op', hrun, hLe, hR4', hF', hfe⟩ := exp_fwd (gL P l) (gLInv P l)
    (hostsSat_lstat S hR'.funcs) hR4 hR'.fnE (S.owned xe hxe) (lowerArgs xe.ty.params ws) run
  obtain ⟨nm, hcx⟩ := S.expGood.core xe hxe
  have hk : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hxs := exp_hxs hcx hT.typed hk
  have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke π' (Ie.addrs.getD xe.core 0)
        ((lowerArgs xe.ty.params ws).map Silmaril.Wasm.SingleThreaded.ofFlat)) (t'.config π₂) :=
    internalP_steps (H := Nat) run
  have hend : (E3 P).status e.1 e.2 = .returned .trap ∨
      ∃ zs, (E3 P).status e.1 e.2 = .returned (.values zs) ∧
        zs.map (·.type) = ValTy.flatList xe.ty.results ∧ liftArgs xe.ty.results zs = none := by
    cases res with
    | trap => exact .inl (status_of_trap (gL P l) hLe final)
    | throw b => exact (not_result_throw hLe final).elim
    | values cvs =>
      obtain ⟨w, hw⟩ := answer_at S.expInst hR'.wfE hk hxs steps (r := .values cvs) final
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ie.exports.get (opAt S.expInst hk hxs).1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
        dsimp only at hw
        split_ifs at hw with ht
        exact ht
      rw [opAt_type] at htyped
      obtain ⟨zs, hm⟩ : ∃ zs, cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs :=
        Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hty : zs.map (·.type) = ValTy.flatList xe.ty.results := by
        have ht := run_typed_at S.expInst hR'.wfE hk hxs steps final hm
        rw [(List.getElem?_eq_some_iff.mp hcx).2] at ht
        exact ht
      have hn : liftArgs xe.ty.results zs = none := by
        simp only [coreRes, hm, liftOutcome] at hout
        revert hout
        cases liftArgs xe.ty.results zs with
        | none => intro _; rfl
        | some _ => intro h; cases h
      exact .inr ⟨zs, status_of_values (gL P l) hLe final hm, hty, hn⟩
  exact ⟨e, hrun, hend, ⟨⟨ρp', Op', ρc, Oc, hR4'⟩, hF',
    hR'.fnC.congr (mapH_funcs_eq _ hfe) rfl, hT.wellFormed S.expInst ⟨nm, hcx⟩ hR'.wfE, hR'.wfI,
    hfe.trans hR'.funcs, hR'.ufuncs, hR'.good⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
