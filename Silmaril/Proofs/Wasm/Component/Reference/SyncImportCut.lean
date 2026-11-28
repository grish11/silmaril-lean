module

public import Silmaril.Wasm.Component.Reference.SyncImportCut.Defs
public import Silmaril.Wasm.Component.SyncImportITree.Thms
import Silmaril.Proofs.Wasm.Component.Reference.CalloutPath

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread decompose? ofFlat profile resumeResult toFlat?)

local notation "E[" o "]" => core3P (profile o)

variable {c : SimpleI} {o : GrowOracle} {σ : Type} {r : Ready c}
  {q : Question (exportIface c)} {f : r.inst.F.Op} {M : Config E[o] σ}
  {m : Question c.imports} {prof : ProfileKind}

private theorem corePrefix {host : Host E[o] σ} {before after : Config E[o] σ}
    {tr : List (Label E[o] σ)} {owner : Option ThreadId} {t : Thread}
    {k : List Flat → P E[o] σ (Ret E[o])} {frames : List (Seg E[o] σ)} {resumers : List (Activation E[o] σ)}
    (run : Steps prof host.hr host.dispatch before tr after) (internal : ∀ l ∈ tr, l = .core)
    (focus : before.ctl = ⟨owner, .core t k, frames⟩ :: resumers) :
    ∃ t', after.ctl = ⟨owner, .core t' k, frames⟩ :: resumers ∧
      Reach (profile o) (refCursor before t) (refCursor after t') := by
  induction run generalizing t with
  | refl => exact ⟨t, focus, .refl⟩
  | cons step rest ih =>
    have label := internal _ List.mem_cons_self
    cases label
    cases step with
    | coreInternal hctl _ hstep =>
      rw [focus] at hctl
      cases hctl
      obtain ⟨t', hfocus, hreach⟩ := ih (fun l hl => internal l (List.mem_cons_of_mem _ hl)) rfl
      exact ⟨t', hfocus, Relation.ReflTransGen.head (internalP_mapH trampIdx hstep) hreach⟩

private theorem importOp_of_flat (r : Ready c) (i : Fin c.imports.length) (ys : List Flat)
    (typed : ys.map (·.type) = ValTy.flatList c.imports[i].2.params) :
    ∃ e, r.inst.importOp? i.val (ys.map ofFlat) = some e := by
  have len : r.inst.imports.length = c.imports.length := by
    rw [r.isInst.2.1, r.good.imports]
    simp
  have hi : i.val < r.inst.imports.length := by simpa only [len] using i.isLt
  have eq' : r.inst.imports[i.val]? = some (fnOf c.imports[i].2.flat) := by
    rw [r.isInst.2.1, r.good.imports, List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem i.isLt]
    rfl
  have eq := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans eq')
  have has : List.Forall₂ ScalarType.HasVal (r.inst.imports.get ⟨i.val, hi⟩).params
      (ys.map ofFlat) := by
    rw [List.get_eq_getElem, eq]
    change List.Forall₂ ScalarType.HasVal ((ValTy.flatList c.imports[i].2.params).map .num) _
    rw [← typed, List.map_map]
    exact forall₂_hasVal_ofFlat ys
  exact ⟨⟨⟨i.val, hi⟩, ⟨ys.map ofFlat, has⟩⟩,
    by simp only [ScalarInstance.importOp?, ifaceOp?, dite_eq_left hi, dite_eq_left has]⟩

private theorem mapM_toFlat {args : List Silmaril.Wasm.Execution.Core.Val} {ys : List Flat}
    (h : args.mapM toFlat? = some ys) : args = ys.map ofFlat := by
  induction args generalizing ys with
  | nil => cases h; rfl
  | cons a as ih =>
    cases hflat : toFlat? a with
    | none => simp [List.mapM_cons, hflat] at h
    | some y =>
      cases hrest : as.mapM toFlat? with
      | none => simp [List.mapM_cons, hflat, hrest] at h
      | some rest =>
        have eq : y :: rest = ys := by simpa [List.mapM_cons, hflat, hrest] using h
        subst ys
        have ea : a = ofFlat y := by
          cases a with
          | num v => cases Option.some.inj hflat; rfl
          | ref _ => cases hflat
          | vec _ => cases hflat
        simp only [List.map_cons, ea, ih hrest]

theorem request {host : Host E[o] σ} {before : Config E[o] σ} {t : Thread} {tr : List (Label E[o] σ)}
    (cut : ReferenceCut M m)
    (focus : before.ctl = ⟨cut.owner, .core t cut.returnTo, cut.frames⟩ :: cut.resumers)
    (run : Steps prof host.hr host.dispatch before tr M) (internal : ∀ l ∈ tr, l = .core) :
    ReachesFront o r q f (refCursor before t) (.request m cut.resume) ∧
    Step prof host.hr host.dispatch M .tau (cut.parked host) := by
  obtain ⟨t', hfocus, reach⟩ := corePrefix run internal focus
  have eq : t' = cut.thread := by
    have activation := (List.cons.inj (hfocus.symm.trans cut.focused)).1
    exact (Focus.core.inj (Activation.mk.inj activation).2.1).1
  subst t'
  obtain ⟨ctx, addr, args, decomp, flat⟩ := status_callout_redex cut.status
  obtain ⟨e, he⟩ := importOp_of_flat r m.index cut.flatArgs cut.flatTypes
  rw [← mapM_toFlat flat] at he
  have ei := ifaceOp?_some he
  have hcall : CalloutAt (refCursor M cut.thread).1 cut.thread m.index.val args :=
    ⟨ctx, addr, by
      let cs : Store (CanonHost E[o]) := M.store.core
      calc
        _ = (decompose? cs (cut.thread.config cs).code).map (mapR trampIdx) :=
          decompose?_config_mapH trampIdx cs cut.thread
        _ = _ := by
          have h : decompose? cs (cut.thread.config cs).code = _ := decomp
          rw [h]
          rfl⟩
  have lifted : liftArgs c.imports[m.index].2.params (e.2.val.filterMap toFlat?) = some m.args.val := by
    rw [ei.2, filterMap_of_mapM flat]
    exact cut.lifted
  exact ⟨.inl ⟨.request e (refCursor M cut.thread), .ucall reach hcall he,
    cutFront_request m ei.1 lifted⟩, .coreCallout cut.focused cut.status⟩

private theorem parked_bind (cut : ReferenceCut M m) (host : Host E[o] σ) :
    (cut.parked host).ctl =
      ⟨cut.owner, .prog (host.dispatch (.hostCallout
        (.lowered ⟨m.index.val⟩ (witFt c.imports[m.index].2) {} ⟨0⟩) cut.flatArgs) >>= Prog.pure),
        .core cut.thread cut.returnTo :: cut.frames⟩ :: cut.resumers := by
  rw [Prog.bind_eq, Prog.bind_pure]
  rfl

theorem answer (r : Ready c)
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)} {s' : σ}
    (cut : ReferenceCut M m) (ready : cut.CanDispatch)
    (a : Values c.imports[m.index].2.results)
    (reply : g M.host ⟨m.index.val⟩ (m.args.val.map toRefVal) = some (a.val.map toRefVal, s')) :
    let host := answerHostS (profile o) g
    ∃ tr resolved next,
      Steps prof host.hr host.dispatch (cut.parked host) tr resolved ∧
      resolved.ctl = ⟨cut.owner, .prog (.pure (.flat (lowerArgs c.imports[m.index].2.results a.val))),
        .core cut.thread cut.returnTo :: cut.frames⟩ :: cut.resumers ∧
      Step prof host.hr host.dispatch resolved .tau next ∧
      next.host = s' ∧ next.store.core = M.store.core ∧
      next.ctl = ⟨cut.owner, .core (cut.resume (some a)).2 cut.returnTo, cut.frames⟩ :: cut.resumers := by
  let host := answerHostS (profile o) g
  let park := cut.parked host
  have mem : c.imports[m.index] ∈ c.imports := List.getElem_mem m.index.isLt
  obtain ⟨pff, rff⟩ := r.floatFree.2 _ mem
  obtain ⟨maxp, maxr, res⟩ := r.arity.2 _ mem
  obtain ⟨st, inst, leave⟩ := ready.mayLeave
  obtain ⟨pos, tr, run⟩ := runs_callout (g := g) (th := cut.owner) (m := park)
    ready.entry inst leave ready.hostFunc pff cut.flatTypes maxp cut.lifted reply res rff a.property maxr
  let flat := lowerArgs c.imports[m.index].2.results a.val
  let result := { park with
    host := s'
    store := calloutSt park.store ⟨0⟩ cut.flatArgs c.imports[m.index].2 pos flat }
  let resolved := { result with
    ctl := ⟨cut.owner, .prog (.pure (.flat flat)),
      .core cut.thread cut.returnTo :: cut.frames⟩ :: cut.resumers }
  have path :=
    (run.lrun_at (prof := prof) (hr := host.hr) ready.unlocked Prog.pure (parked_bind cut host)).steps
  have storeCore : resolved.store.core = M.store.core := by
    change (calloutSt park.store ⟨0⟩ cut.flatArgs c.imports[m.index].2 pos flat).core = M.store.core
    rw [calloutSt_eq]
    rfl
  let next := { resolved with
    ctl := ⟨cut.owner, .core (E[o].resume resolved.store.core cut.thread (.values flat))
      cut.returnTo, cut.frames⟩ :: cut.resumers }
  refine ⟨tr, resolved, next, path, rfl, .popCore rfl, rfl, storeCore, ?_⟩
  have same : E[o].resume resolved.store.core cut.thread (.values flat) = (cut.resume (some a)).2 := by
    rw [storeCore, resume_values]
    exact (resumeResult_mapH trampIdx _ _ _).symm
  change _ :: _ = _
  rw [same]

theorem refuses (r : Ready c)
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}
    (cut : ReferenceCut M m) (ready : cut.CanDispatch)
    (reply : g M.host ⟨m.index.val⟩ (m.args.val.map toRefVal) = none) :
    let host := answerHostS (profile o) g
    ∃ tr pre reason,
      Steps prof host.hr host.dispatch (cut.parked host) tr pre ∧
      Step prof host.hr host.dispatch pre (.trap reason) (trapCfg pre) := by
  let host := answerHostS (profile o) g
  let park := cut.parked host
  have mem : c.imports[m.index] ∈ c.imports := List.getElem_mem m.index.isLt
  obtain ⟨st, inst, leave⟩ := ready.mayLeave
  obtain ⟨tr, pre, run⟩ := traps_callout_host (g := g) (th := cut.owner) (m := park)
    ready.entry inst leave ready.hostFunc (r.floatFree.2 _ mem).1 cut.flatTypes
    (r.arity.2 _ mem).1 cut.lifted reply
  obtain ⟨p, frames, reason, run, _, step⟩ := run.lrun (prof := prof) (hr := host.hr)
    ready.unlocked Prog.pure (.core cut.thread cut.returnTo :: cut.frames) cut.resumers
  have eq := congrArg (fun ctl => { park with ctl := ctl }) (parked_bind cut host).symm
  rw [eq] at run
  exact ⟨tr, _, reason, run.steps, step.1⟩

end Silmaril.Proofs.Wasm.Component.Reference.SyncImportCut
