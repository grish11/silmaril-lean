module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Thms
import Silmaril.Wasm.Game.Linking.Trap.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnLive

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Numerics Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn

@[expose] def observed (bytes : ByteArray) : Callout := ⟨("wit", "node"), nodeArgs, some bytes⟩

@[expose] def decoded : Nat → Op ownSig := fun rep => ⟨OwnTag.res, (rep, ())⟩

theorem attempt_on_slice {store : Store Nat} {mem : MemInst} (rt : RT)
    (found : store.mems[0]? = some mem) (width : mem.type.address = .i32)
    (payload : (observed mem.bytes).segment 16 4 = some [1, 0, 0, 0])
    (children : (observed mem.bytes).segment 0 0 = some []) :
    contract.attempt (some 0) rt ⟨0, store, nodeArgs⟩ =
      ((lookupChecked rt 0 1).map fun rep => ((decoded rep, []), rt.killAll [1])).mapError
        .resource := by
  have callout : checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩ = .ok (observed mem.bytes) := by
    simp [checkedCallout, found, width, requireSome, bind, Except.bind, pure, Except.pure, observed]
  have contents : decodeNodePayload (Nested.rawSignature ownSig) {}
      ⟨OwnTag.res, 16, 0, 0⟩ (observed mem.bytes) = .ok (⟨OwnTag.res, ((1 : UInt32), ())⟩, []) := by
    unfold decodeNodePayload
    change (requireSome NodeIssue.payloadOutOfBounds ((observed mem.bytes).segment 16 4)).bind
      (fun area => _) = _
    rw [payload]
    dsimp only [requireSome, Except.bind, Nat.mul_zero]
    rw [children]
    have fields : readFieldsWith (checkedPayloadReader .utf8 (observed mem.bytes))
        [.u32] 0 [1, 0, 0, 0] = some ((1 : UInt32), ()) := by
      simp only [readFieldsWith, readValWith, checkedPayloadReader]
      rfl
    change (requireSome NodeIssue.badPayload (readFieldsWith
      (checkedPayloadReader .utf8 (observed mem.bytes)) [.u32] 0 [1, 0, 0, 0])).bind _ = _
    rw [fields]
    simp only [requireSome, bind, Except.bind, pure, Except.pure,
      HandleAccept.Memory.le32s, ownSig, Formats.Arity.Admits]
    rfl
  change (checkedAt {} ("wit", "node") 0 ⟨0, store, nodeArgs⟩
    (Nested.checkedNode ownSig ownTagOf {} rt)) = _
  unfold checkedAt
  change (checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩).bind _ = _
  rw [callout]
  change (decodeNodePayload (Nested.rawSignature ownSig) {} ⟨OwnTag.res, 16, 0, 0⟩
    (observed mem.bytes)).bind _ = _
  rw [contents]
  have schema : checkPTys .recursiveOwn [.own 0] = .ok () := rfl
  simp only [bind, Except.bind, Nested.reserveOp, ownSig, Nested.resolveTypes, Nested.resolveTypesWith,
    Nested.resolveWith,
    Nested.reserve, StateT.run, StateT.bind, StateT.pure, get, getThe, MonadStateOf.get,
    set, schema, Except.mapError, pure, Except.pure, StateT.get,
    List.not_mem_nil, UInt32.toBitVec_ofNat]
  cases lookupChecked rt 0 (1#32) <;> rfl

private theorem memory32 {c : Config Nat} (prepared : prep ownMod = some (c, none))
    {mem : MemInst} (one : c.store.mems = [mem]) : mem.type.address = .i32 := by
  have address : ((prep ownMod).map fun result =>
      result.1.store.mems.map (·.type.address)) = some [.i32] := by decide +kernel
  simpa [prepared, one] using address

private theorem map_imports {types : List DefType} {imports : List FnType}
    (typed : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) types imports) :
    types.map FnType.ofDefType? = imports.map some := by
  induction typed with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head, ih]

private theorem no_call_tags (call : Option Callout) : call.elim [] roles.callTags = [] := by
  cases call <;> rfl

private theorem no_answer_tags (call : Option Callout) (reply : HostReply) :
    (call.elim [] fun observed => roles.answerTags observed reply) = [] := by
  cases call <;> rfl

theorem audited_accepts_then_traps (P : Profile) (rt : RT) (rep : Nat)
    (entry : rt 1 = some ⟨0, rep, true⟩) :
    ∃ mt instanceInfo initial, IsSpecInstance ownMod mt instanceInfo initial ∧
      contract.link ownMod instanceInfo initial 0 = .ok (some 0) ∧
      ∃ afterAccept afterTrap : Store Nat,
        TSession P (Audit.env contract (some 0)) ownMod (some 0) roles initial ⟨⟨rt, {}⟩, []⟩
          instanceInfo.addrs .idle false
          (⟨afterAccept, {}, []⟩, ⟨⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩, acceptedEntries⟩)
          [.enter none, .exit (some ())] ∧
        contract.attempt (some 0) (rt.killAll [1]) ⟨0, afterTrap, nodeArgs⟩ = .error (.resource (.dead 1)) ∧
        TSession P (Audit.env contract (some 0)) ownMod (some 0) roles initial ⟨⟨rt, {}⟩, []⟩
          instanceInfo.addrs .idle false
          (⟨afterTrap, {}, [.trap]⟩, ⟨⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩, rejectedEntries⟩)
          [.enter none, .exit (some ()), .enter none, .exit none] := by
  obtain ⟨mt, inst, preparedConfig, hi⟩ := spec_exists ownSpec_some
  obtain ⟨initial, start, prepared, rfl, -, exports⟩ := prep_of_spec hi
  obtain ⟨rfl, empty, memories, exportList, memLength, node, accept, run, funcs, nodeOk,
    acceptOk, runOk⟩ := own_facts prepared
  rw [show initial.withStart none = initial from rfl] at hi
  obtain ⟨mem, one, size⟩ := one_page ownMem prepared
  have width := memory32 prepared one
  have linked : contract.link ownMod inst initial 0 = .ok (some 0) := by
    unfold Contract.link
    rw [memories]
    have valid : validate? ownMod = some mt := hi.valid
    have imported : (CExternType.funcs mt.imports).map FnType.ofDefType? =
        [some contract.importType, some ⟨[.num (.int .i32)], []⟩] := by
      have computed : (validate? ownMod).map (fun type =>
          (CExternType.funcs type.imports).map FnType.ofDefType?) =
          some [some contract.importType, some ⟨[.num (.int .i32)], []⟩] := by decide +kernel
      simpa [valid] using computed
    have selected : inst.imports[0]? = some contract.importType := by
      have eq := (map_imports hi.importTypes).symm.trans imported
      have first : (inst.imports.map some)[0]? = some (some contract.importType) :=
        congrArg (fun types : List (Option FnType) => types[0]?) eq
      rw [List.getElem?_map] at first
      cases actual : inst.imports[0]? with
      | none => rw [actual] at first; cases first
      | some type => rw [actual] at first; cases first; rfl
    change (if _ then _ else _) = _
    simp [contract, ownMod, selected]
    rfl
  obtain ⟨_, _, nodeCode, nodeType, nodeIndex⟩ := stubOk_spec nodeOk
  obtain ⟨_, _, acceptCode, acceptType, acceptIndex⟩ := stubOk_spec acceptOk
  obtain ⟨code, params, results, runCode, locals, body, runType, noParams, noResults,
    runFuncs, runMems, -⟩ := fnOk_spec runOk
  let frame := Frame.forCall run.module [] [.i32, .i32]
  have frameFuncs : frame.module.funcs = [0, 1, 2] := by simp [frame, Frame.forCall, runFuncs]
  have frameMems : frame.module.mems = [0] := by simp [frame, Frame.forCall, runMems]
  let nodeCtx := bodyCtx frame (expression (ownBody.drop 8))
  let acceptCtx := bodyCtx frame []
  have exportRun : 2 ∈ inst.addrs := by rw [← exports, exportList]; simp
  have lookup (store : Store Nat) (same : store.funcs = initial.store.funcs) :
      store.funcs[0]? = some node ∧ store.funcs[1]? = some accept ∧ store.funcs[2]? = some run := by
    rw [same, funcs]; exact ⟨rfl, rfl, rfl⟩
  have wellTyped (store : Store Nat) (same : store.funcs = initial.store.funcs) : InvokeOk store 2 [] :=
    ⟨run, params, results, (lookup store same).2.2, runType, by
      rw [List.eq_nil_of_length_eq_zero (l := params.toList) noParams]; exact .nil⟩
  have reachNode (store : Store Nat) (memory : MemInst)
      (same : store.funcs = initial.store.funcs) (oneMem : store.mems = [memory])
      (large : memory.bytes.size = 65536) (addr : memory.type.address = .i32) :
      ∃ next : Store Nat, ∃ updated : MemInst,
        next.funcs = initial.store.funcs ∧ next.mems = [updated] ∧ updated.bytes.size = 65536 ∧
        updated.type.address = .i32 ∧
        (∀ table, contract.attempt (some 0) table ⟨0, next, nodeArgs⟩ =
          ((lookupChecked table 0 1).map fun repr => ((decoded repr, []), table.killAll [1])).mapError .resource) ∧
        ∃ target : Config Nat, target.store = next ∧ target.frame = {} ∧
          Steps P NH (invoke store 2 []) target ∧
          decompose? next target.code = some (nodeCtx, 0, 0, nodeArgs) := by
    have enter : Step P NH (invoke store 2 [])
        ⟨store, {}, [.frame 0 frame [.label 0 [] (expression ownBody)]]⟩ := by
      have step := Step.callRefFunc (P := P) (host := NH) (s := store) (f := {})
        (c := .callRefType ((store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
        (a := 2) (fi := run) (code := code) trivial (lookup store same).2.2 runType
        (by rw [noParams]; rfl) runCode
      rw [noResults, locals, body] at step
      exact step
    obtain ⟨bytes, written⟩ := store_some (B := memory.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
      (n := IntType.i32.width / 8) ((1 : BitVec 32).setWidth _) (by rw [large]; decide)
    let updated : MemInst := { memory with bytes }
    let next := store.setMem 0 updated
    have nextMem : next.mems = [updated] := by simp [next, Store.setMem, oneMem]
    have nextFuncs : next.funcs = initial.store.funcs := same
    have put : Step P NH ⟨store, {}, [.frame 0 frame [.label 0 [] (expression ownBody)]]⟩
        ⟨next, {}, [.frame 0 frame [.label 0 [] (expression (ownBody.drop 3))]]⟩ :=
      step_body (step_mid [] _ (step_store32 frameMems (by rw [oneMem]; rfl) written))
    have call : Step P NH ⟨next, {}, [.frame 0 frame [.label 0 [] (expression (ownBody.drop 3))]]⟩
        ⟨next, {}, nodeCtx.fill (vals nodeArgs ++ [.ref (.func 0), .callRefType node.type])⟩ :=
      step_body (step_mid nodeArgs _ (step_call (x := ⟨0⟩) (by rw [frameFuncs]; rfl) (lookup next nextFuncs).1))
    have payload := segment_of_store written (observed bytes) rfl
    have encoded : (Memory.encodeLE 4 1).data.toList = [1, 0, 0, 0] := by decide +kernel
    change (observed bytes).segment 16 4 = some (Memory.encodeLE 4 1).data.toList at payload
    rw [encoded] at payload
    have children := segment_nil (o := observed bytes) rfl 0 (Nat.zero_le bytes.size)
    have big : updated.bytes.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store written).trans large
    refine ⟨next, updated, nextFuncs, nextMem, big, addr, fun table => ?_, _, rfl, rfl,
      (enter.steps.trans put.steps).trans call.steps, ?_⟩
    · exact attempt_on_slice (mem := updated) table (by rw [nextMem]; rfl) addr payload children
    · exact decompose_fill _ trivial (lookup next nextFuncs).1 nodeType (by rw [nodeIndex]; rfl) nodeCode
  obtain ⟨afterAccept, memAfter, same, memOne, memSize, memWidth, firstAttempt, target,
    rfl, targetFrame, steps, redex⟩ := reachNode initial.store mem rfl one size width
  let startSession : TSession P (Audit.env contract (some 0)) ownMod (some 0) roles
      initial ⟨⟨rt, {}⟩, []⟩ inst.addrs .inst false (initial, ⟨⟨rt, {}⟩, []⟩) [] := .start
  have firstCall := TSession.call (TSession.of_core_steps
    (TSession.invoke startSession (by decide) ⟨[], empty⟩ exportRun (wellTyped initial.store rfl)) steps) redex
  have success : contract.attempt (some 0) rt ⟨0, target.store, nodeArgs⟩ =
      .ok ((decoded rep, []), rt.killAll [1]) := by
    rw [firstAttempt]
    have live : lookupChecked rt 0 1 = .ok rep := by unfold lookupChecked; rw [entry]; rfl
    rw [live]; rfl
  let pending : State Writer := ⟨rt.killAll [1], ⟨some (resTree rep), []⟩⟩
  let accepted : State Writer := ⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩
  have nodeAnswer : Session.Answer contract (some 0) ⟨rt, {}⟩ ⟨0, target.store, nodeArgs⟩
      ⟨target.store, .values [.i32 9]⟩ pending := by
    apply Session.Answer.returnHandle rfl success ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  let committed : Audit.Event := ⟨0, nodeArgs, .values [.i32 9], .committed⟩
  have nodeLog : Audit.observe contract (some 0) ⟨rt, {}⟩ ⟨0, target.store, nodeArgs⟩
      ⟨target.store, .values [.i32 9]⟩ = committed := by
    simp only [Audit.observe, show contract.code = (0 : Nat) from rfl, ite_true, success, committed]
  have firstAnswer := TSession.answer firstCall redex (a := ⟨target.store, .values [.i32 9]⟩)
    (q' := Audit.Journal.mk pending [committed]) (by exact ⟨nodeAnswer, congrArg (· :: []) nodeLog.symm⟩)
  have goAccept : Step P NH ⟨target.store, target.frame, nodeCtx.fill (Result.values [.i32 9]).toAdmin⟩
      ⟨target.store, target.frame, acceptCtx.fill (vals [.i32 9] ++ [.ref (.func 1), .callRefType accept.type])⟩ :=
    step_body (step_mid [.i32 9] [] (step_call (x := ⟨1⟩) (by rw [frameFuncs]; rfl) (lookup _ same).2.1))
  have acceptRedex : decompose? target.store
      (acceptCtx.fill (vals [.i32 9] ++ [.ref (.func 1), .callRefType accept.type])) =
      some (acceptCtx, 1, 1, [.i32 9]) :=
    decompose_fill _ trivial (lookup _ same).2.1 acceptType (by rw [acceptIndex]; rfl) acceptCode
  have acceptCall := TSession.call (TSession.of_core_steps firstAnswer goAccept.steps) acceptRedex
  have acceptedAnswer : Session.Answer contract (some 0) pending ⟨1, target.store, [.i32 9]⟩
      ⟨target.store, .values []⟩ accepted := by
    apply Session.Answer.other (by change (1 : Nat) ≠ 0; decide)
    exact ⟨rfl, rfl, rfl, resTree rep, rfl, rfl⟩
  have acceptAnswer := TSession.answer acceptCall acceptRedex (a := ⟨target.store, .values []⟩)
    (q' := Audit.Journal.mk accepted acceptedEntries) (by exact ⟨acceptedAnswer, rfl⟩)
  have finish : Steps P NH ⟨target.store, target.frame, acceptCtx.fill (Result.values []).toAdmin⟩
      ⟨target.store, {}, []⟩ := by
    rw [targetFrame]
    exact (Step.ctxtFrame (Step.labelVals (vs := []))).steps.trans (Step.frameVals (vs := []) rfl).steps
  have firstDone := TSession.ret (TSession.of_core_steps acceptAnswer finish) (r := .values []) rfl
  obtain ⟨_, _, _, _, _, _, retryAttempt, retry, sameStore, retryFrame, retrySteps, retryRedex⟩ :=
    reachNode target.store memAfter same memOne memSize memWidth
  have retryCall : decompose? retry.store retry.code = some (nodeCtx, 0, 0, nodeArgs) :=
    sameStore ▸ retryRedex
  have secondCall := TSession.call (TSession.of_core_steps
    (TSession.invoke firstDone (by decide) ⟨.values [], rfl⟩ exportRun (wellTyped _ same)) retrySteps)
    retryCall
  have rejected : contract.attempt (some 0) accepted.resources ⟨0, retry.store, nodeArgs⟩ =
      .error (.resource (.dead 1)) := by
    rw [sameStore, retryAttempt]
    have dead : lookupChecked (rt.killAll [1]) 0 1 = .error (.dead 1) := by
      have killed : (rt.killAll [1]) 1 = some ⟨0, rep, false⟩ := by
        unfold RT.killAll
        rw [ite_eq_left (List.mem_cons_self ..), entry]
        rfl
      unfold lookupChecked
      rw [killed]
      rfl
    rw [show accepted.resources = rt.killAll [1] from rfl, dead]; rfl
  have deadAnswer : Session.Answer contract (some 0) accepted ⟨0, retry.store, nodeArgs⟩
      ⟨retry.store, .trap⟩ accepted := .reject rfl rejected
  have trapLog : Audit.observe contract (some 0) accepted ⟨0, retry.store, nodeArgs⟩
      ⟨retry.store, .trap⟩ = ⟨0, nodeArgs, .trap, .rejected (.resource (.dead 1))⟩ := by
    simp only [Audit.observe, show contract.code = (0 : Nat) from rfl, ite_true, rejected]
  have trapAnswer := TSession.answer secondCall retryCall
    (a := ⟨retry.store, .trap⟩) (q' := Audit.Journal.mk accepted rejectedEntries)
    (by exact ⟨deadAnswer, congrArg (· :: acceptedEntries) trapLog.symm⟩)
  have unwind := Linking.fill_trap_steps P retry.store nodeCtx retry.frame
  have trapDone := TSession.ret (TSession.of_core_steps trapAnswer unwind) (r := .trap) rfl
  rw [retryFrame] at trapDone
  simp [no_call_tags, no_answer_tags, Roles.exitVal] at firstDone trapDone
  refine ⟨mt, inst, initial, hi, linked, target.store, retry.store, ?_, rejected, ?_⟩
  · simpa [roles, accepted] using firstDone
  · simpa [roles, accepted] using trapDone

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay
