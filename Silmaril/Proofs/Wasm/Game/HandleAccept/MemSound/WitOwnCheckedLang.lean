module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Thms
import Silmaril.Wasm.Game.IOAccept.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnCheckedLang

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay
  Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Logic.Hoare
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReplay
open Silmaril.Accept.IO (Tag)
open Silmaril.Wasm.Logic.Core (Post)

private def shapeRoles : Roles Unit Callout Unit Unit where
  callIn := some

private def nodeShape (observed : Callout) : Prop :=
  observed.args = nodeArgs ∧ observed.segment 16 4 = some [1, 0, 0, 0] ∧
    observed.segment 0 0 = some []

private def shapeContract : MemContract Callout where
  pre observed := observed.imp = ("wit", "node") → nodeShape observed
  reply := hiReply

private theorem shape_body {P : Profile} {node accept : FuncInst Nat}
    (nodeOk : stubOk 0 4 node = true) (acceptOk : stubOk 1 1 accept = true)
    {frame : Frame} (funcs : frame.module.funcs = [0, 1, 2]) (mems : frame.module.mems = [0])
    {store : Store Nat} {code : List (FuncInst Nat)}
    (prefixCode : code = [node, accept] ++ code.drop 2) (sameCode : store.funcs = code)
    (oneMemory : store.mems.length = 1)
    (invariant : ∀ next, next.funcs = code → next.mems.length = 1 → ownInv next)
    {post : Post Nat} (postOk : BodyExits ownInv post) :
    HWP P (memHost ownMod (some 0) shapeRoles shapeContract) store frame
      (vals [] ++ expression ownBody) post := by
  obtain ⟨_, _, nodeCode, nodeType, nodeParams⟩ := stubOk_spec nodeOk
  obtain ⟨_, _, acceptCode, acceptType, acceptParams⟩ := stubOk_spec acceptOk
  have atNode : ∀ next : Store Nat, next.funcs = code → next.funcs[0]? = some node := by
    intro next same; rw [same, prefixCode]; rfl
  have atAccept : ∀ next : Store Nat, next.funcs = code → next.funcs[1]? = some accept := by
    intro next same; rw [same, prefixCode]; rfl
  have trap : ∀ next nextFrame, next.funcs = code → next.mems.length = 1 → post next nextFrame .trap :=
    fun next nextFrame same one => (postOk next (invariant next same one) nextFrame).2.2.1
  have throw : ∀ next nextFrame address, next.funcs = code → next.mems.length = 1 →
      post next nextFrame (.throw address) :=
    fun next nextFrame address same one => (postOk next (invariant next same one) nextFrame).2.2.2 address
  unfold ownBody
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.store32 (us := []) mems oneMemory (trap store frame sameCode oneMemory)
    fun memory bytes _ written => ?_
  obtain ⟨_, oneWritten, codeWritten⟩ := setMem_mems (mi := { memory with bytes }) oneMemory
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := nodeArgs) (x := ⟨0⟩) (k := 0) (fk := node)
    (i := impNode) (by rw [funcs]; rfl) (atNode _ (codeWritten.trans sameCode)) nodeCode nodeType
    (by simp [nodeArgs, nodeParams]) rfl ?_ ?_
  · intro _
    exact ⟨rfl, segment_of_store written _ (memOf_setMem oneMemory),
      segment_nil (memOf_setMem oneMemory) 0 (Nat.zero_le _)⟩
  rintro after result ⟨⟨codeAfter, oneAfter⟩, resultShape⟩ _
  have codeSame := codeAfter.trans (codeWritten.trans sameCode)
  have memorySame := oneAfter.trans oneWritten
  refine ⟨fun values returned => ?_, fun _ => trap after frame codeSame memorySame,
    fun address _ => throw after frame address codeSame memorySame⟩
  obtain ⟨handle, rfl⟩ := (resultShape values returned).1 rfl
  subst returned
  refine hwp_call (us := []) (args := [.i32 handle]) (x := ⟨1⟩) (k := 1) (fk := accept)
    (i := WitAst.impAcc) (by rw [funcs]; rfl) (atAccept _ codeSame) acceptCode acceptType
    (by simp [acceptParams]) rfl (fun wrong => False.elim ((by decide :
      ("wit", "accept") ≠ ("wit", "node")) wrong)) ?_
  rintro final result ⟨⟨codeFinal, oneFinal⟩, shape⟩ _
  have finalCode := codeFinal.trans codeSame
  have finalMemory := oneFinal.trans memorySame
  refine ⟨fun values returned => ?_, fun _ => trap final frame finalCode finalMemory,
    fun address _ => throw final frame address finalCode finalMemory⟩
  obtain rfl := (shape values returned).2 rfl
  exact X.done (postOk final (invariant final finalCode finalMemory) frame).1

private theorem shape_sat (P : Profile) : MemSat P ownMod 0 shapeRoles shapeContract ownInv := by
  intro moduleType inst initial linked
  obtain ⟨prepared, start, prepEq, rfl, _, exportEq⟩ := prep_of_spec linked
  obtain ⟨rfl, empty, mems, exports, one, node, accept, run, funcs, nodeOk, acceptOk, runOk⟩ :=
    own_facts prepEq
  have memory : (prepared.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, mems]
  rw [memory]
  refine ⟨fun steps => Safe.of_exits (o := .normal []) (by simp [Config.withStart, empty]; rfl)
    (fun _ _ => ⟨prepared, none, prepEq, rfl, one⟩), ?_⟩
  intro address exported
  rw [← exportEq, exports] at exported
  obtain rfl : address = 2 := by simpa using exported
  obtain ⟨bodyCode, _, _, runCode, locals, body, runType, params, results, frameFuncs, frameMems, _⟩ :=
    fnOk_spec runOk
  have bodyInv : ∀ next, next.funcs = prepared.store.funcs → next.mems.length = 1 → ownInv next :=
    fun next same memory => ⟨prepared, none, prepEq, same, memory⟩
  have sameFuncs : ∀ store, ownInv store → store.funcs = prepared.store.funcs := by
    rintro store ⟨base, baseStart, basePrep, same, _⟩
    have eq : base = prepared := (Prod.mk.inj (Option.some.inj (basePrep.symm.trans prepEq))).1
    rw [same, eq]
  refine export_valid (fi := run) (fun store inv => by rw [sameFuncs store inv, funcs]; rfl)
    runCode runType results ?_
  intro store args inv typed post postOk
  have correctArgs := args_length (by rw [sameFuncs store inv, funcs]; rfl) runType typed
  rw [params] at correctArgs
  have noArgs := List.eq_nil_of_length_eq_zero correctArgs
  subst args
  rw [body, locals]
  have storeMemory : store.mems.length = 1 := by obtain ⟨_, _, _, _, mem⟩ := inv; exact mem
  exact shape_body nodeOk acceptOk (by simp [Frame.forCall, frameFuncs])
    (by simp [Frame.forCall, frameMems]) (code := prepared.store.funcs) (by rw [funcs]; rfl)
    (sameFuncs store inv) storeMemory bodyInv postOk

private theorem reply_shape {before after : State Writer} {call : UCall Nat} {reply : UReply}
    (answer : Answer contract (some 0) before call reply after) : hiReply call reply := by
  cases answer with
  | reject => exact ⟨⟨rfl, rfl⟩, fun _ impossible => by cases impossible⟩
  | decline => exact ⟨⟨rfl, rfl⟩, fun _ impossible => by cases impossible⟩
  | returnHandle node _ keeps _ =>
    refine ⟨keeps, fun _ returned => ?_⟩
    cases returned
    exact ⟨fun _ => ⟨_, rfl⟩, fun accept => by cases (show (0 : Nat) = 1 from node.symm.trans accept)⟩
  | other _ writer =>
    obtain ⟨accept, _, rfl, _⟩ := writer
    refine ⟨⟨rfl, rfl⟩, fun _ returned => ?_⟩
    cases returned
    constructor
    · intro node; cases (show (1 : Nat) = 0 from accept.symm.trans node)
    · exact fun _ => rfl

private theorem call_tag {P : Profile} {init current : Config Nat} {initial state : State Writer}
    {exports : List Nat} {phase : Phase} {pending : Bool} {tags} {ctx : Ctx} {address : Nat}
    {args : List Val} {obs : Callout}
    (history : TSession P (contract.env (some 0)) ownMod (some 0) shapeRoles init
      initial exports phase pending (current, state) tags)
    (redex : decompose? current.store current.code = some (ctx, address, 0, args))
    (observed : calloutAt? ownMod (some 0) current = some obs) :
    ∃ before, TSession P (contract.env (some 0)) ownMod (some 0) shapeRoles init
      initial exports phase true (current, state) (before ++ [.inp obs]) := by
  have tag : (calloutAt? ownMod (some 0) current).elim [] shapeRoles.callTags = [.inp obs] := by
    rw [observed]; rfl
  cases pending with
  | false => exact ⟨tags, tag ▸ TSession.call history redex⟩
  | true =>
    cases history with
    | call previous decompose => exact ⟨_, tag ▸ TSession.call previous decompose⟩

private theorem callout_shape {P : Profile} {mt : CModuleType} {inst : ScalarInstance}
    {init current : Config Nat} {initial state : State Writer} {phase : Phase} {pending : Bool}
    {tags} {ctx : Ctx} {address : Nat} {args : List Val}
    (linked : IsSpecInstance ownMod mt inst init) (mem : init.frame.module.mems[0]? = some 0)
    (history : TSession P (contract.env (some 0)) ownMod (some 0) roles init
      initial inst.addrs phase pending (current, state) tags)
    (redex : decompose? current.store current.code = some (ctx, address, 0, args)) :
    nodeShape ⟨("wit", "node"), args, memOf (some 0) current.store⟩ := by
  let obs : Callout := ⟨("wit", "node"), args, memOf (some 0) current.store⟩
  have observed : calloutAt? ownMod (some 0) current = some obs := by
    unfold calloutAt?
    rw [redex]; rfl
  obtain ⟨seenPhase, _, _, _, retagged⟩ := IOAccept.Session.exists_tsession
    (m := ownMod) (memAddr := some 0) (R := shapeRoles) history.toSession
  obtain ⟨before, tagged⟩ := call_tag retagged redex observed
  have trace : before ++ [.inp obs] ∈ tagTraces P (ReplyEnvs hiReply) 0 ownMod shapeRoles := by
    refine ⟨mt, inst, init, linked, contract.env (some 0), initial,
      fun _ _ _ _ answer => reply_shape answer, seenPhase, true, (current, state), ?_⟩
    rw [mem]; exact tagged
  obtain ⟨callout, shape, seen | ⟨_, seen⟩⟩ := tagTraces_pre (K := shapeContract)
    (shape_sat P) (fun _ _ admitted => admitted) trace (v := []) (u := before)
    rfl (fun _ _ => trivial)
  · change some callout = some obs at seen
    cases seen
    exact shape rfl
  · cases seen

private theorem attempt_success {store : Store Nat} {args : List Val} {rt : RT}
    {op : Op ownSig} {children : List (BitVec 32)} {updated : RT}
    (shape : nodeShape ⟨("wit", "node"), args, memOf (some 0) store⟩)
    (success : contract.attempt (some 0) rt ⟨0, store, args⟩ = .ok ((op, children), updated)) :
    ∃ rep, lookupChecked rt 0 1 = .ok rep ∧
      op = decoded rep ∧ children = [] ∧ updated = rt.killAll [1] := by
  obtain ⟨rfl, payload, empty⟩ := shape
  cases found : store.mems[0]? with
  | none =>
    have wrong : checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩ = .error .missingMemory := by
      simp [checkedCallout, found, requireSome, bind, Except.bind]
    change (checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩).bind _ = _ at success
    rw [wrong] at success
    cases success
  | some memory =>
    by_cases width : memory.type.address = .i32
    · have bytes : memOf (some 0) store = some memory.bytes := by simp [memOf, found]
      rw [show (⟨("wit", "node"), nodeArgs, memOf (some 0) store⟩ : Callout) =
        observed memory.bytes from by rw [bytes, observed]] at payload empty
      rw [attempt_on_slice rt found width payload empty] at success
      cases result : lookupChecked rt 0 1 with
      | error issue => rw [result] at success; cases success
      | ok rep =>
        rw [result] at success
        cases success
        exact ⟨rep, rfl, rfl, rfl, rfl⟩
    · have wrong : checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩ =
          .error (.addressWidth memory.type.address) := by
        simp [checkedCallout, found, width, requireSome, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw]
      change (checkedCallout ("wit", "node") 0 ⟨0, store, nodeArgs⟩).bind _ = _ at success
      rw [wrong] at success
      cases success

private inductive WriterState (rt : RT) : State Writer → Prop where
  | empty : WriterState rt ⟨rt, {}⟩
  | pending {rep : Nat} : rt 1 = some ⟨0, rep, true⟩ →
      WriterState rt ⟨rt.killAll [1], ⟨some (resTree rep), []⟩⟩
  | accepted {rep : Nat} : rt 1 = some ⟨0, rep, true⟩ →
      WriterState rt ⟨rt.killAll [1], ⟨none, [resTree rep]⟩⟩

private theorem slot_entry {rt : RT} {rep : Nat} (looked : lookupChecked rt 0 1 = .ok rep) :
    rt 1 = some ⟨0, rep, true⟩ := by
  cases entry : rt (1#32) with
  | none => simp [lookupChecked, entry] at looked
  | some raw =>
    obtain ⟨kind, representation, live⟩ := raw
    cases live with
    | false => simp [lookupChecked, entry] at looked
    | true =>
      by_cases same : kind = 0
      · subst kind
        simp [lookupChecked, entry] at looked
        subst rep
        rfl
      · simp [lookupChecked, entry, same] at looked

private theorem spent {rt : RT} {rep : Nat} (entry : rt 1 = some ⟨0, rep, true⟩) :
    lookupChecked (rt.killAll [1]) 0 1 = .error (.dead 1) := by
  simp only [lookupChecked, RT.killAll, List.mem_cons_self, ite_true, entry]
  rfl

private theorem step_writer {rt : RT} {before after : State Writer} {call : UCall Nat} {reply : UReply}
    (previous : WriterState rt before)
    (shape : call.target = contract.code → nodeShape ⟨("wit", "node"), call.args,
      memOf (some 0) call.store⟩)
    (answer : Answer contract (some 0) before call reply after) : WriterState rt after := by
  cases answer with
  | reject | decline => exact previous
  | @returnHandle op children updated handle store writer node successful _ wrote =>
    have actual : (⟨0, call.store, call.args⟩ : UCall Nat) = call := by
      rw [show (0 : Nat) = call.target from node.symm]
    have success : contract.attempt (some 0) before.resources ⟨0, call.store, call.args⟩ =
        .ok ((op, children), updated) := by rw [actual]; exact successful
    obtain ⟨rep, looked, rfl, rfl, rfl⟩ := attempt_success (shape node) success
    obtain ⟨wasEmpty, _, _, changed⟩ := wrote
    cases previous with
    | empty =>
      simp only [decoded] at changed
      rw [changed]
      exact .pending (slot_entry looked)
    | pending _ => cases wasEmpty
    | accepted entry => rw [spent entry] at looked; cases looked
  | other _ wrote =>
    obtain ⟨_, _, _, tree, wasPending, rfl⟩ := wrote
    cases previous with
    | empty | accepted _ => cases wasPending
    | pending entry => cases wasPending; exact .accepted entry

private theorem writer_state {P : Profile} {rt : RT} {mt : CModuleType} {inst : ScalarInstance}
    {init : Config Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × (contract.env (some 0)).S} {tags}
    (linked : IsSpecInstance ownMod mt inst init) (mem : init.frame.module.mems[0]? = some 0)
    (history : TSession P (contract.env (some 0)) ownMod (some 0) roles init
      ⟨rt, {}⟩ inst.addrs phase pending current tags) : WriterState rt current.2 := by
  induction history with
  | start => exact .empty
  | internal _ _ ih | call _ _ ih | invoke _ _ _ _ _ ih | ret _ _ ih => exact ih
  | @answer _ _ _ _ _ _ _ hostCode _ _ history redex answer ih =>
    refine step_writer ih (fun code => ?_) answer
    change hostCode = 0 at code
    exact callout_shape linked mem history (by rw [← code]; exact redex)

theorem language_eq (P : Profile) (rt : RT) :
    language P rt = {tree | ∃ rep, rt 1 = some ⟨0, rep, true⟩ ∧ tree = resTree rep} := by
  ext tree
  constructor
  · rintro ⟨mt, inst, init, linked, memory, link, _, _, _, _, _, history, accepted⟩
    obtain ⟨prepared, start, prepEq, rfl, _, _⟩ := prep_of_spec linked
    obtain ⟨rfl, _, mems, _⟩ := own_facts prepEq
    have mem : (prepared.withStart none).frame.module.mems[0]? = some 0 := by
      simp [Config.withStart, mems]
    have withMemory : memory = some 0 := by
      have correctName : (ownMod.imports[contract.code]?.map fun item =>
          (item.moduleName, item.name)) = some contract.name := rfl
      have correctCount : (ownMod.imports.filter fun item =>
          (item.moduleName, item.name) == contract.name).length = 1 := rfl
      simp only [Contract.link, correctName, correctCount, ne_self_iff_false, ite_false] at link
      split at link
      · cases link
      · exact (Except.ok.inj link).symm.trans mem
    subst memory
    have observed := writer_state linked mem history
    cases observed with
    | empty | pending _ => cases accepted
    | accepted entry => exact ⟨_, entry, List.mem_singleton.mp accepted⟩
  · rintro ⟨rep, entry, rfl⟩
    obtain ⟨mt, inst, init, linked, memory, store, _, history, _, _⟩ :=
      accepts_then_traps P rt rep entry
    exact ⟨mt, inst, init, linked, some 0, memory, .idle, false, ⟨store, {}, []⟩, _, _, history,
      List.mem_cons_self ..⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnCheckedLang
