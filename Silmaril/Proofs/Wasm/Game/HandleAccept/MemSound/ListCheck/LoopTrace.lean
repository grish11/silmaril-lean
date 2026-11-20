module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopModule
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
import Silmaril.Wasm.Game.IOAccept.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (stubOk stubOk_spec fnOk_spec prep_of_spec)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live (decompose_fill step_call)
open Silmaril.Wasm.Logic.Core (Step.ctx Steps.append)

variable {pages : InitialPages}

private def loopCtx (frame : Frame) (deep : Ctx) : Ctx :=
  .frame [] 0 frame (.label [] 0 [] (.label [] 0 body deep []) []) []

def running (outer frame : Frame) (store : Store Nat) (code : List Admin) : Config Nat :=
  ⟨store, outer, [.frame 0 frame [.label 0 [] [.label 0 body code]]]⟩

private abbrev NoHost : HostSemantics Nat := fun _ _ _ _ => False

private theorem in_loop {profile : Profile} {store : Store Nat} {outer frame next : Frame}
    {code after : List Admin}
    (run : Steps profile NoHost ⟨store, frame, code⟩ ⟨store, next, after⟩) :
    Steps profile NoHost (running outer frame store code) (running outer next store after) :=
  run.label.label.frame

private def importIx (ix : ListImports) (slot : Nat) : String × String :=
  if slot = 0 then ix.items else if slot = 1 then ix.child else ix.accept

private theorem call_reduces {profile : Profile} {store : Store Nat} {frame : Frame}
    {func : FuncInst Nat} {idx : FuncIdx} {slot : Nat} {args : List Val} {tail : List Admin}
    (localFunc : frame.module.funcs[idx.toNat]? = some slot) (storeFunc : store.funcs[slot]? = some func) :
    Steps profile NoHost ⟨store, frame, vals args ++ .plain (.call idx) :: tail⟩
      ⟨store, frame, (Ctx.top [] tail).fill (vals args ++ [.ref (.func slot), .callRefType func.type])⟩ := by
  have step := Step.ctx (P := profile) (host := NoHost) args tail
    (step_call (x := idx) (F := frame) localFunc storeFunc)
  simpa only [Ctx.fill, vals, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append]
    using step.steps

private theorem reply_in_loop {profile : Profile} {ix : ListImports} {L : SEnv UImp} {module_ : Module}
    (imports : module_.imports = (Loop.mod ix).imports)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {initial : Config Nat} {initState : L.S} {exports : List Nat}
    {store next : Store Nat} {outer frame : Frame} {q nextState : L.S}
    {tags : List (Tag Unit MemREv Unit Unit)} {args : List Val} {tail : List Admin}
    {idx : FuncIdx} {func : FuncInst Nat} (which : idx = ⟨0⟩ ∨ idx = ⟨1⟩)
    (separate : ix.accept ≠ ix.items ∧ ix.accept ≠ ix.child)
    (localFunc : frame.module.funcs[idx.toNat]? = some idx.toNat)
    (storeFunc : store.funcs[idx.toNat]? = some func)
    (stub : stubOk idx.toNat 2 func = true) (arity : args.length = 2)
    (answer : L.Ans q ⟨idx.toNat, store, args⟩ ⟨next, .values []⟩ nextState)
    (session : TSession profile L module_ (some 0) (listRoles ix ans)
      initial initState exports .run false
      (running outer frame store (vals args ++ .plain (.call idx) :: tail), q) tags) :
    TSession profile L module_ (some 0) (listRoles ix ans) initial initState exports .run false
      (running outer frame next tail, nextState)
      (tags ++ (listRoles ix ans).answerTags ⟨importIx ix idx.toNat, args, memOf (some 0) store⟩
        ⟨.values [], memOf (some 0) next⟩) := by
  let context := loopCtx frame (.top [] tail)
  let code := vals args ++ [.ref (.func idx.toNat), .callRefType func.type]
  let stopped : Config Nat := ⟨store, outer, context.fill code⟩
  have steps : Steps profile NoHost
      (running outer frame store (vals args ++ .plain (.call idx) :: tail)) stopped :=
    in_loop (call_reduces localFunc storeFunc)
  obtain ⟨params, results, hostCode, expanded, count⟩ := stubOk_spec stub
  have decompose : decompose? store stopped.code = some (context, idx.toNat, idx.toNat, args) := by
    exact decompose_fill context trivial storeFunc expanded (arity.trans count.symm) hostCode
  have callout : calloutAt? module_ (some 0) stopped =
      some ⟨importIx ix idx.toNat, args, memOf (some 0) store⟩ := by
    unfold calloutAt?
    change (decompose? store stopped.code).bind _ = _
    rw [decompose, imports]
    rcases which with rfl | rfl <;> rfl
  have noCallTag : (listRoles ix ans).callTags ⟨importIx ix idx.toNat, args, memOf (some 0) store⟩ = [] := by
    rcases which with rfl | rfl <;>
      simp [Roles.callTags, listRoles, readAccept, ListImports.toRead, importIx, Idx.toNat,
        Ne.symm separate.1, Ne.symm separate.2]
  have reached := TSession.of_core_steps session steps
  have called := TSession.call reached decompose
  have replied := TSession.answer called decompose answer
  rw [callout] at replied
  simpa [Option.elim, noCallTag, stopped, context, loopCtx, Ctx.fill, running, Result.toAdmin, vals]
    using replied

private theorem accept_in_loop {profile : Profile} {ix : ListImports} {L : SEnv UImp} {module_ : Module}
    (imports : module_.imports = (Loop.mod ix).imports)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {initial : Config Nat} {initState : L.S} {exports : List Nat}
    {store : Store Nat} {outer frame : Frame} {q : L.S} {root : BitVec 32}
    {tags : List (Tag Unit MemREv Unit Unit)} {func : FuncInst Nat}
    (localFunc : frame.module.funcs[2]? = some 2) (storeFunc : store.funcs[2]? = some func)
    (stub : stubOk 2 1 func = true)
    (session : TSession profile L module_ (some 0) (listRoles ix ans)
      initial initState exports .run false (running outer frame store
        (.label 0 [] (vals [.i32 root] ++ expression [.call ⟨2⟩, .return_]) ::
          expression (iteration.drop 8)), q) tags) :
    ∃ stopped, TSession profile L module_ (some 0) (listRoles ix ans) initial initState exports
      .run true (stopped, q) (tags ++ [.inp (.accept root)]) := by
  let context := loopCtx frame (.label [] 0 [] (.top [] (expression [.return_]))
    (expression (iteration.drop 8)))
  let code := vals [.i32 root] ++ [.ref (.func 2), .callRefType func.type]
  let stopped : Config Nat := ⟨store, outer, context.fill code⟩
  have calls : Steps profile NoHost
      ⟨store, frame, vals [.i32 root] ++ expression [.call ⟨2⟩, .return_]⟩
      ⟨store, frame, (Ctx.top [] (expression [.return_])).fill code⟩ :=
    call_reduces (idx := ⟨2⟩) localFunc storeFunc
  have reached : TSession profile L module_ (some 0) (listRoles ix ans) initial initState exports
      .run false (stopped, q) tags :=
    TSession.of_core_steps session (in_loop (Steps.append (expression (iteration.drop 8)) calls.label))
  obtain ⟨params, results, hostCode, expanded, count⟩ := stubOk_spec stub
  have decompose : decompose? store stopped.code = some (context, 2, 2, [.i32 root]) :=
    decompose_fill context trivial storeFunc expanded (by rw [count]; rfl) hostCode
  have callout : calloutAt? module_ (some 0) stopped =
      some ⟨ix.accept, [.i32 root], memOf (some 0) store⟩ := by
    unfold calloutAt?
    change (decompose? store stopped.code).bind _ = _
    rw [decompose, imports]
    rfl
  refine ⟨stopped, ?_⟩
  have called := TSession.call reached decompose
  rw [callout] at called
  simpa [Roles.callTags, listRoles, readAccept, ListImports.toRead, Callout.args1, Callout.i32?, Val.i32]
    using called

theorem drive {profile : Profile} {ix : ListImports} {L : SEnv UImp} {module_ : Module}
    (imports : module_.imports = (Loop.mod ix).imports)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {ready : Store Nat → Prop}
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready ans root handles answerFor)
    (names : ix.child ≠ ix.items ∧ ix.accept ≠ ix.items ∧ ix.accept ≠ ix.child)
    {inst : ModuleInst} (localFuncs : inst.funcs = [0, 1, 2, 3]) (localMems : inst.mems = [0])
    {items child accept check : FuncInst Nat} (itemsStub : stubOk 0 2 items = true)
    (childStub : stubOk 1 2 child = true) (acceptStub : stubOk 2 1 accept = true)
    {initial : Config Nat} {initState : L.S} {exports : List Nat} {outer : Frame}
    {index base offset : BitVec 32} {store : Store Nat} {q : L.S}
    {tags : List (Tag Unit MemREv Unit Unit)} (bounded : index.toNat ≤ handles.length)
    (atStore : store.funcs = [items, child, accept, check]) (good : ready store)
    (session : TSession profile L module_ (some 0) (listRoles ix ans) initial initState exports
      .run false (running outer (locals inst root index base offset) store (expression iteration), q) tags) :
    ∃ stopped lastState, TSession profile L module_ (some 0) (listRoles ix ans) initial initState exports
      .run true (stopped, lastState) (tags ++ (remainingReads root handles (handles.drop index.toNat) answerFor).map .inp) := by
  let frame := locals inst root index base offset
  have args : Steps profile NoHost ⟨store, frame, expression iteration⟩
      ⟨store, frame, vals [.i32 root, .i32 0] ++ expression (iteration.drop 2)⟩ :=
    Silmaril.Wasm.Logic.Core.exec_sound (expression (iteration.drop 2))
      (rs := []) (rs' := [.i32 0, .i32 root]) (is := iteration.take 2) rfl
  have readyToCall := TSession.of_core_steps session (in_loop args)
  obtain ⟨itemsStore, itemsState, memory, itemReply, itemsGood, itemsFuncs, memAt, decoded, width⟩ :=
    plan.items store q good
  have itemRead := reply_in_loop (idx := ⟨0⟩) imports (Or.inl rfl) names.2
    (by change inst.funcs[0]? = some 0; rw [localFuncs]; rfl)
    (by change store.funcs[0]? = some items; rw [atStore]; rfl) itemsStub rfl itemReply readyToCall
  have itemsTag : (listRoles ix ans).answerTags
      ⟨importIx ix 0, [.i32 root, .i32 0], memOf (some 0) store⟩
      ⟨.values [], memOf (some 0) itemsStore⟩ = [.inp (.read (.items root) (.items handles))] := by
    simp [Roles.answerTags, listRoles, listRead, importIx, itemsRead, itemsAns, ListImports.toRead,
      memOf, memAt, decoded, Val.i32]
  simp only [show (⟨0⟩ : FuncIdx).toNat = 0 from rfl, itemsTag] at itemRead
  have memIdx : inst.mems[0]? = some 0 := by rw [localMems]; rfl
  by_cases done : index.toNat = handles.length
  · have taking := to_accept (profile := profile) (host := NoHost) (base := base) (offset := offset)
      (root := root) memIdx memAt decoded done
    have branch := TSession.of_core_steps itemRead (in_loop taking)
    obtain ⟨stopped, reached⟩ := accept_in_loop (func := accept) imports
      (by change inst.funcs[2]? = some 2; rw [localFuncs]; rfl)
      (by rw [itemsFuncs, atStore]; rfl) acceptStub branch
    refine ⟨stopped, itemsState, ?_⟩
    simpa [remainingReads, done, List.append_assoc] using reached
  · have before : index.toNat < handles.length := by omega
    obtain ⟨newBase, guard, steps⟩ := to_child (profile := profile) (host := NoHost) (store := itemsStore)
      (root := root) (oldBase := base) (oldOffset := offset) memIdx memAt decoded before width
    have atChild := TSession.of_core_steps itemRead (in_loop steps)
    let handle := handles[index.toNat]
    obtain ⟨next, nextState, childReply, nextGood, nextFuncs, answerEq⟩ :=
      plan.child handle (List.getElem_mem before) itemsStore itemsState itemsGood
    have readChild := reply_in_loop (idx := ⟨1⟩) imports (Or.inr rfl) names.2
      (by change inst.funcs[1]? = some 1; rw [localFuncs]; rfl)
      (by change itemsStore.funcs[1]? = some child; rw [itemsFuncs, atStore]; rfl) childStub rfl childReply atChild
    have childTag : (listRoles ix ans).answerTags
        ⟨importIx ix 1, [.i32 handle, .i32 0], memOf (some 0) itemsStore⟩
        ⟨.values [], memOf (some 0) next⟩ = [.inp (.read (.atom handle) (answerFor handle))] := by
      simpa [Roles.answerTags, listRoles, listRead, importIx, childRead, names.1, Val.i32]
        using answerEq
    simp only [show (⟨1⟩ : FuncIdx).toNat = 1 from rfl, childTag] at readChild
    have bump := back_edge (profile := profile) (host := NoHost) (store := next) (inst := inst)
      (root := root) (index := index) (base := newBase) (offset := index * 4)
    have repeatRound := TSession.of_core_steps readChild bump.label.frame
    obtain ⟨last, lastState, reached⟩ := drive imports plan names localFuncs localMems itemsStub childStub acceptStub
      (index := index + 1) (by rw [next_index guard]; omega) (nextFuncs.trans (itemsFuncs.trans atStore))
      nextGood repeatRound
    refine ⟨last, lastState, ?_⟩
    rw [next_index guard] at reached
    unfold remainingReads at reached ⊢
    rw [List.drop_eq_getElem_cons before]
    simpa only [List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append, List.append_assoc]
      using reached
termination_by handles.length - index.toNat
decreasing_by exact remaining_decreases guard before

theorem input_map (reads : List MemREv) :
    Silmaril.Wasm.Game.HandleAccept.Memory.inputsOf (X := Unit) (O := Unit) (C := Unit)
      (some .enter) (reads.map .inp) = reads := by
  induction reads with
  | nil => rfl
  | cons event rest ih => simp [Silmaril.Wasm.Game.HandleAccept.Memory.inputsOf, ih]

theorem trace {profile : Profile} {ix : ListImports} (valid : LoopSound.shapeOk ix pages = true)
    (separate : ix.accept ≠ ix.items ∧ ix.accept ≠ ix.child)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod ix pages) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L)
    (initState : L.S) {ready : Store Nat → Prop} (good : ready initial.store)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready ans root handles answerFor) :
    .enter :: remainingReads root handles handles answerFor ∈ listTraces profile Envs 0 (Loop.mod ix pages) ix ans := by
  obtain ⟨cfg, start, prepared, rfl, _, exported⟩ := prep_of_spec spec
  obtain ⟨distinct, rfl, noCode, mems, exports, _, items, child, accept, check, storeFuncs,
    itemsStub, childStub, acceptStub, declared, checkShape⟩ := LoopSound.shape_facts valid prepared
  obtain ⟨code, params, results, codeIs, localTypes, instrs, expanded, paramsLen, resultsLen,
    localFuncs, localMems, defaults⟩ := fnOk_spec checkShape
  have atCheck : cfg.store.funcs[3]? = some check := by rw [storeFuncs]; rfl
  have canInvoke : InvokeOk cfg.store 3 [.i32 root] := by
    have signature := Expand.iff.1 expanded
    rw [declared] at signature
    change some (Ty.func (Ty.ofList [.i32]) .nil) = some (Ty.func params results) at signature
    obtain ⟨rfl, rfl⟩ := Ty.func.inj (Option.some.inj signature)
    exact ⟨check, _, _, atCheck, expanded, .cons (.num _) .nil⟩
  have initialSession : TSession profile L (Loop.mod ix pages) (some 0) (listRoles ix ans)
      (cfg.withStart none) initState instance_.addrs .inst false (cfg.withStart none, initState) [] := .start
  have exportedCheck : 3 ∈ instance_.addrs := by rw [← exported, exports]; simp
  have called := initialSession.invoke (by decide) ⟨[], noCode⟩ exportedCheck canInvoke
  have frameEq : Frame.forCall check.module [.i32 root] code.locals = locals check.module root 0 0 0 := by
    unfold Frame.forCall
    rw [localTypes, defaults]
    rfl
  have enterCheck := Step.callRefFunc (P := profile) (host := NoHost) (s := cfg.store) (f := {})
    (c := .callRefType ((cfg.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [.i32 root])
    trivial atCheck expanded (by rw [paramsLen]; rfl) codeIs
  rw [frameEq, resultsLen, instrs] at enterCheck
  have enterLoop : Step profile NoHost ⟨cfg.store, locals check.module root 0 0 0, expression body⟩
      ⟨cfg.store, locals check.module root 0 0 0, [.label 0 body (expression iteration)]⟩ :=
    Step.loop (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have loop := TSession.of_core_steps called (enterCheck.steps.trans enterLoop.steps.label.frame)
  obtain ⟨stopped, lastState, reached⟩ := drive (module_ := Loop.mod ix pages) rfl plan ⟨distinct, separate⟩ localFuncs localMems
    itemsStub childStub acceptStub (index := 0) (by simp) storeFuncs good loop
  have memoryAddr : (cfg.withStart none).frame.module.mems[0]? = some 0 := by rw [show (cfg.withStart none).frame.module.mems = cfg.frame.module.mems from rfl, mems]; rfl
  refine ⟨.enter none :: (remainingReads root handles handles answerFor).map .inp,
    ⟨mt, instance_, cfg.withStart none, spec, L, initState, env, .run, true, (stopped, lastState), ?_⟩, ?_⟩
  · rw [memoryAddr]
    exact reached
  · change .enter :: Silmaril.Wasm.Game.HandleAccept.Memory.inputsOf (some .enter)
      ((remainingReads root handles handles answerFor).map .inp) = _
    rw [input_map]

theorem accepts_trace {profile : Profile} {ix : ListImports} {module_ : Module}
    {Envs : Store Nat → SEnv UImp → Prop}
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (transcript : .enter :: remainingReads root handles handles answerFor ∈ listTraces profile Envs 0 module_ ix ans)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {rho : Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom, answerFor handle = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile Envs 0 module_ ix ans .trap policy Rhos := by
  let Reader := sexpR MemAtom (BitVec 32)
  let tree := SExp.ofList children
  have atItems : RStep Reader .trap policy rho .live (.read (.items root) (.items handles)) .live ∅ := by
    have validQuery : Reader.valid rho (.items root) := ⟨children, rootDenotes⟩
    exact .read (S := {a | Reader.ok rho (.items root) a})
      (by simp only [answers, ite_eq_left validQuery]) ⟨children, rootDenotes, denotes⟩
  have atChild (handle : BitVec 32) (member : handle ∈ handles) :
      RStep Reader .trap policy rho .live (.read (.atom handle) (answerFor handle)) .live ∅ := by
    obtain ⟨atom, answer, names⟩ := atoms handle member
    rw [answer]
    have validQuery : Reader.valid rho (.atom handle) := ⟨atom, names⟩
    exact .read (S := {a | Reader.ok rho (.atom handle) a})
      (by simp only [answers, ite_eq_left validQuery]) names
  let readerHost := reader Reader .trap policy rho
  have rest (unread : List (BitVec 32)) (included : ∀ handle ∈ unread, handle ∈ handles) :
      (reader Reader .trap policy rho).Run .live (remainingReads root handles unread answerFor) .live {tree} := by
    induction unread with
    | nil =>
      have run := Host.Run.cons (h := readerHost) atItems
        (Host.Run.cons (RStep.acceptOk (R := Reader) (pol := .trap) (onAccept := policy) rootDenotes) (.nil _))
      simpa [remainingReads, tree] using run
    | cons handle tail ih =>
      have run := Host.Run.cons (h := readerHost) atItems (Host.Run.cons (atChild handle (included handle (by simp)))
        (ih (fun item found => included item (List.mem_cons_of_mem _ found))))
      simpa [remainingReads] using run
  have run := Host.Run.cons (h := readerHost) (RStep.enter (R := Reader) (pol := .trap) (onAccept := policy) (ρ := rho))
    (rest handles (fun _ found => found))
  simp only [listReaderLang, readerLang, langOver, Host.lang]
  refine Set.mem_iUnion.2 ⟨⟨rho, allowed⟩, Set.mem_biUnion transcript ?_⟩
  exact ⟨_, _, run, by simp [tree]⟩

theorem accepts {profile : Profile} {ix : ListImports} (valid : LoopSound.shapeOk ix pages = true)
    (separate : ix.accept ≠ ix.items ∧ ix.accept ≠ ix.child)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod ix pages) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L)
    (initState : L.S) {ready : Store Nat → Prop} (good : ready initial.store)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready ans root handles answerFor)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {rho : Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom, answerFor handle = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile Envs 0 (Loop.mod ix pages) ix ans .trap policy Rhos :=
  accepts_trace (trace valid separate spec env initState good plan) policy allowed rootDenotes denotes atoms

theorem checker_accepts_pages {profile : Profile} (checker : Checker)
    (shape : LoopSound.shapeOk checker.imports pages = true)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports pages) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L)
    (initState : L.S) {ready : Store Nat → Prop} (good : ready initial.store)
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready checker.decodeChild root handles answerFor)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {rho : Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom, answerFor handle = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile Envs 0 (Loop.mod checker.imports pages) checker.imports
      checker.decodeChild .trap policy Rhos := by
  cases checker
  · exact accepts shape (by decide) spec env initState good plan policy allowed rootDenotes denotes atoms
  · exact accepts shape (by decide) spec env initState good plan policy allowed rootDenotes denotes atoms

theorem checker_shape (checker : Checker) : LoopSound.shapeOk checker.imports = true := by
  cases checker
  · exact LoopSound.sym_shape
  · exact LoopSound.blob_shape

theorem checker_bounded_pages (profile : Profile) (checker : Checker)
    (shape : LoopSound.shapeOk checker.imports pages = true) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy envs ⊆ boundedListsOf checker.kind := by
  cases checker
  · exact ListCheck.listReaderLang_subset (fun env => LoopSound.sat profile shape ListCheck.symTextAns_kind env)
      (fun _ _ same => same) noUB envs
  · exact ListCheck.listReaderLang_subset (fun env => LoopSound.sat profile shape ListCheck.blobAns_kind env)
      (fun _ _ same => same) noUB envs

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
