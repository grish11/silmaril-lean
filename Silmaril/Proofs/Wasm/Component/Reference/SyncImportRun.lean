module

public import Silmaril.Wasm.Component.Reference.SyncImportRun.Defs
public import Silmaril.Wasm.Component.Reference.SyncImportCut.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SoundI

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.SyncImportRun

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store Result)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread profile ofFlat resumeResult)

local notation "P[" o "]" => profile o
local notation "E[" o "]" => core3P (profile o)

variable {c : SimpleI} {o : GrowOracle} {r : Ready c} {q : Question (exportIface c)}
  {op : r.inst.F.Op} {σ : Type}
  {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}

private theorem observes_segment
    {B : CStore E[o]} {th : Option ThreadId} {x y : CoreSt E[o]} {s s' : σ}
    {calls : List (σ × CallRec × σ)} {rounds : List (Round r.inst.E)}
    {a : Values (exportIface c)[q.index].2.results} {w : r.inst.F.Ar op}
    {vs : List Silmaril.Wasm.Execution.Core.Val}
    (seg : ASeg g (SiteI c) B th s x calls s' y)
    (rel : List.Forall₂ (RoundOf c r.inst g) calls rounds)
    (done : (y.2.config (Store.mapH trampIdx y.1)).code = (Result.values vs).toAdmin)
    (typed : Answer.ofResult? (r.inst.exports.get op.1) (.values vs) = some w)
    (lifted : cutFront r q (f := op) (.reply w (Store.mapH trampIdx y.1)) =
      .reply (some a) (Store.mapH trampIdx y.1)) :
    ∃ cs, HostReplies (c := c) g s cs s' ∧
      Observes o r q op (Store.mapH trampIdx x.1, x.2) cs
        (.reply (some a) (Store.mapH trampIdx y.1)) := by
  induction seg generalizing rounds with
  | done steps =>
    cases rel
    exact ⟨[], .nil _, .reply (.inl ⟨.reply w _, .oret
      (reach_mapH trampIdx (coreSteps_internalP steps)) done typed, lifted⟩)⟩
  | @call s s₁ s' x p y L ys flat ctx addr args rest steps _ _ _ _ atCall _ ih =>
    cases rel with
    | @cons _ round _ rounds link tail =>
      obtain ⟨imp, answered⟩ := round
      obtain ⟨nameTy, ws, us, found, liftedArgs, reply, typedReply, result⟩ := link.2.2
      have bound : imp.1.val < c.imports.length := (List.getElem?_eq_some_iff.mp found).1
      let i : Fin c.imports.length := ⟨imp.1.val, bound⟩
      have eq := (List.getElem?_eq_some_iff.mp found).2
      change c.imports[i] = nameTy at eq
      subst nameTy
      let m : Question c.imports := ⟨i, ⟨ws, checkList_of_liftArgs liftedArgs⟩⟩
      let a₁ : Values c.imports[m.index].2.results := ⟨us, typedReply⟩
      have impIdx : imp.1.val = L.f.idx := (ifaceOp?_some link.1).1
      have here : CalloutAt (Store.mapH trampIdx p.1) p.2 imp.1.val args :=
        ⟨ctx, addr, by erw [decompose?_config_mapH, atCall, impIdx]; rfl⟩
      have imported : r.inst.importOp? imp.1.val args = some imp := by
        rw [impIdx]
        exact link.1
      have reached : ReachesCut o r.inst op (Store.mapH trampIdx x.1, x.2)
          (.request imp (Store.mapH trampIdx p.1, p.2)) :=
        .ucall (reach_mapH trampIdx (coreSteps_internalP steps)) here imported
      have front := cutFront_request (r := r) (q := q) (f := op) (p := (Store.mapH trampIdx p.1, p.2))
        (e := imp) m rfl liftedArgs
      obtain ⟨cs, host, obs⟩ := ih tail done lifted
      have actualResult : Answer.toResult (ft := r.inst.imports.get imp.1) answered =
          .values (flat.map ofFlat) := link.2.1
      change Answer.toResult (ft := r.inst.imports.get imp.1) answered = _ at result
      change Observes o r q op (Store.mapH trampIdx p.1, (E[o]).resume p.1 p.2 (.values flat)) cs _ at obs
      erw [resume_values, ← resumeResult_mapH trampIdx, ← actualResult, result] at obs
      exact ⟨⟨m, some a₁⟩ :: cs, .cons reply host, .answer (some a₁)
        (.inl ⟨.request imp _, reached, front⟩) obs⟩

theorem sees_of_reference_return (r : Ready c) (wired : c.Inst)
    (q : Question (exportIface c)) {prof : ProfileKind} {s₀ : σ}
    {ready finished : Config E[o] σ}
    {inst : InstId} {exports : List (String × FuncId)} {f : FuncId} {rs : List Reference.Val}
    (typedHost : c.HostOkS g)
    (init : let h := answerHostS P[o] g
      Instantiates prof h.hr h.dispatch (Config.init (hostFuncs 0 c.imports CStore.empty) s₀)
        c.toRef (importArgs c.imports) ready inst exports)
    (lookup : exports.lookup (exportIface c)[q.index].1 = some f)
    (run : let h := answerHostS P[o] g
      Calls prof h.hr h.dispatch ready ⟨0⟩ f (q.args.val.map toRefVal) finished
        (.resolved (some rs))) :
    ∃ (a : Values (exportIface c)[q.index].2.results) (cs : List (Call (signature c.imports))),
      a.val.map toRefVal = rs ∧ HostReplies (c := c) g s₀ cs finished.host ∧
      Sees ((body o r q).run ⟨r.inst.store⟩).run cs
        (.reply (some a) (Store.mapH trampIdx finished.store.core)) := by
  obtain ⟨I, cs, hI, hcs, tramp, instantiated⟩ := instPhaseIS P[o] prof c r.good wired r.arity
  have same : I = r.inst := ImpModule.IsInst.unique hI r.isInst
  subst I
  have hm := instantiated σ (answerHostS P[o] g) s₀ (.instance ready inst exports) init
  obtain ⟨rfl, rfl, rfl⟩ := InstResult.instance.inj hm
  let j : Fin c.exports.length := Fin.cast (by simp [exportIface]) q.index
  let exp := c.exports[j]
  have exportEq : (exportIface c)[q.index] = (exp.name, exp.ty) := List.getElem_map ..
  have argsTyped : ValTy.checkList exp.ty.params q.args.val = true := by
    simpa only [exportEq] using q.args.property
  have hf : f = ⟨c.imports.length + j.val⟩ :=
    Option.some.inj ((exportEq ▸ lookup).symm.trans (exportMapI_lookup r.good j j.isLt))
  subst f
  obtain ⟨op, entryEq⟩ := entry_exists r q
  have entryCore : ifaceOp? r.inst.exports exp.core
      ((lowerArgs exp.ty.params q.args.val).map ofFlat) = some op := by
    unfold entry at entryEq
    simpa only [exportEq] using entryEq
  obtain ⟨opIdx, opArgs⟩ := ifaceOp?_some entryCore
  let addr := r.inst.addrs.getD exp.core 0
  have start : CallStart c r.inst cs op addr (lowerArgs exp.ty.params q.args.val) :=
    ⟨r.good, r.isInst, hcs, by
      change r.inst.addrs.getD op.1.val 0 = r.inst.addrs.getD exp.core 0
      rw [opIdx], opArgs⟩
  have threadEq : r.inst.initThread op = Thread.invokeFlat addr (lowerArgs exp.ty.params q.args.val) := by
    change Thread.pending (r.inst.addr op.1) op.2.1 = _
    rw [start.addr, start.args]
    rfl
  have mem : exp ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨name, flat⟩ := r.good.core exp mem
  have flatTy : r.inst.exports.get op.1 = fnOf exp.ty.flat := by
    have eq : r.inst.exports[op.1.val]? = some (fnOf exp.ty.flat) := by
      rw [opIdx, r.isInst.2.2, List.getElem?_map, flat]
      rfl
    exact Option.some.inj ((List.getElem?_eq_getElem op.1.isLt).symm.trans eq)
  obtain ⟨maxParams, maxResult, oneResult⟩ := r.arity.1 _ mem
  obtain ⟨paramsFloatFree, resultFloatFree⟩ := r.floatFree.1 _ mem
  obtain ⟨M, th, k, frames, rest, entryTrace, pre, atCore, hostEq⟩ := call_atA (g := g) prof cs
    (c.afterFuncs P[o] fun i => r.inst.addrs.getD i 0) s₀ (c.imports.length + j.val) addr exp
    q.args.val paramsFloatFree argsTyped maxParams oneResult maxResult resultFloatFree
    (afterFuncs_lifted _ j.isLt)
  have guards := calloutsOk_of (s₀ := M.host) start r.floatFree r.arity tramp typedHost
    ⟨atCore.funcs, atCore.entry, atCore.inst⟩
  obtain ⟨trace, steps, hostEvents, _, holds⟩ := run
  obtain ⟨_, invoke, afterInvoke⟩ := Steps.cons_iff.mp steps
  rcases pre.inv (invoke_invA invoke ▸ afterInvoke) with live | ⟨tr, htr, fromCore⟩
  · exact False.elim (live.not_holds _ _ holds)
  rw [coreCfg_start atCore] at fromCore
  obtain ⟨calls, s', y, seg, exits | fails⟩ :=
    segs_inv atCore.lock tr.length _ _ [] [] tr finished _ le_rfl guards fromCore holds
  · obtain ⟨ST, CL, preCore, label, afterCore, postCore, hseg, noCallout, exit, suffix⟩ := exits
    have laterHostEvents : ∀ ev, Label.host ev ∈ postCore → CallHostEvent ⟨0⟩ ev := by
      intro ev he
      exact hostEvents ev (htr ▸ List.mem_append_right _ (hseg ▸ List.mem_append_right _ he))
    rcases exit with ⟨ys, status, -, rfl⟩ | ⟨_, -, rfl⟩ | ⟨h, ys, status⟩
    · obtain ⟨vs, code, flatResult⟩ := status_values status
      obtain ⟨rounds, w, _, rel, _, checked⟩ := path_returned start seg (.values vs) code
      have types := results_typed flatTy checked flatResult
      cases lifted : liftArgs exp.ty.results ys with
      | none =>
        cases out_of_trapsNextA (atCore.trap s' ST CL y ys types lifted) suffix holds
      | some ws =>
        obtain ⟨returned, finalCore, finalHost⟩ := result_of_resolvesA
          (atCore.ret s' ST CL y ys ws types lifted) suffix laterHostEvents holds
        cases returned
        let a : Values (exportIface c)[q.index].2.results :=
          ⟨ws, by rw [exportEq]; exact checkList_of_liftArgs lifted⟩
        have code' : (y.2.config (Store.mapH trampIdx y.1)).code = (Result.values vs).toAdmin := by
          erw [config_mapH trampIdx]
          exact code
        have front : cutFront r q (f := op) (.reply w (Store.mapH trampIdx y.1)) =
            .reply (some a) (Store.mapH trampIdx y.1) := by
          have eq : liftArgs (exportIface c)[q.index].2.results ys = some a.val := by
            change liftArgs (exportIface c)[q.index].2.results ys = some ws
            simpa only [exportEq] using lifted
          simp only [cutFront, answerPayload_of_ofResult? checked, flatResult, Option.map_some,
            Option.bind_some, liftValues, Option.pmap_some' eq]
        obtain ⟨calls, replies, seen⟩ := observes_segment seg rel code' checked front
        change finished.store.core = y.1 at finalCore
        change finished.host = s' at finalHost
        rw [← hostEq, finalHost, finalCore]
        refine ⟨a, calls, rfl, replies, (body_sees_iff entryEq).mpr ?_⟩
        rw [threadEq, ← hcs]
        exact seen
    · rw [steps_of_locked rfl rfl suffix] at holds
      cases holds_trapCfgA holds
    · exact (noCallout h ys status).elim
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, impossible⟩ := fails
    cases impossible

end Silmaril.Proofs.Wasm.Component.Reference.SyncImportRun
