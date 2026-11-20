module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopCompact
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.ReserveReplay
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
import Silmaril.Wasm.Game.IOAccept.Thms
import Silmaril.Wasm.Verify.Check.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingTrace

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing (reserve reply)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
open GrowingModule (initialMem initial_bytes initial_pages)
open LoopRun (locals drive input_map accepts_trace bytes_plan)

private theorem reserveStore {profile : Profile} {store : Store Nat} {pages : InitialPages}
    (allocated : store.mems = [initialMem pages]) (requested : InitialPages)
    (allows : pages.val < requested.val →
      profile.growMaySucceed .memory 0 pages.val (requested.val - pages.val)) :
    ∃ reached, reached.funcs = store.funcs ∧ ReplySpace (max pages.val requested.val * 65536) reached ∧
      ReserveReplay.Succeeds profile store reached (initialMem pages) (BitVec.ofNat 32 requested.val) := by
  have requestedNat : (BitVec.ofNat 32 requested.val).toNat = requested.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := requested.property; omega)]
  have beforePages := initial_pages pages
  by_cases needs : pages.val < requested.val
  · have canGrow : ∃ grown, (initialMem pages).grow? (requested.val - pages.val) = some grown ∧
        grown.bytes.size = requested.val * 65536 := by
      unfold MemInst.grow?
      dsimp only
      split
      · refine ⟨_, rfl, ?_⟩
        change ((initialMem pages).bytes ++
          ⟨Array.replicate ((requested.val - pages.val) * 65536) 0⟩).size = _
        rw [ByteArray.size_append]
        change (initialMem pages).bytes.size +
          (Array.replicate ((requested.val - pages.val) * 65536) (0 : UInt8)).size = _
        rw [Array.size_replicate, initial_bytes]
        omega
      · rename_i denied
        exfalso
        apply denied
        constructor
        · change (initialMem pages).pages + (requested.val - pages.val) ≤ 65536
          rw [beforePages]
          have bound := requested.property
          omega
        · simp [initialMem, memoryType]
    obtain ⟨grown, growth, size⟩ := canGrow
    use store.setMem 0 grown
    refine ⟨rfl, ⟨grown, by simp [Store.setMem, allocated], ?_⟩, ?_⟩
    · simpa only [Nat.max_eq_right (Nat.le_of_lt needs)] using size
    · unfold ReserveReplay.Succeeds
      rw [requestedNat, beforePages]
      exact .inr ⟨needs, grown, growth, allows needs, rfl⟩
  · have enough := Nat.le_of_not_lt needs
    refine ⟨store, rfl, ⟨initialMem pages, allocated, ?_⟩, ?_⟩
    · simpa only [Nat.max_eq_left enough] using initial_bytes pages
    · unfold ReserveReplay.Succeeds
      rw [requestedNat, beforePages]
      exact .inl ⟨enough, rfl⟩

private theorem trace {profile : Profile} {ix : ListImports} {pages : InitialPages}
    (names : ix.child ≠ ix.items ∧ ix.accept ≠ ix.items ∧ ix.accept ≠ ix.child)
    (requested : InitialPages) (allows : pages.val < requested.val →
      profile.growMaySucceed .memory 0 pages.val (requested.val - pages.val))
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Growing.mod ix pages) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L) (initState : L.S)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {root : BitVec 32}
    {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L (ReplySpace (max pages.val requested.val * 65536)) ans root handles answerFor) :
    .enter :: remainingReads root handles handles answerFor ∈ listTraces profile Envs 0 (Growing.mod ix pages) ix ans := by
  obtain ⟨cfg, start, prepared, rfl, _, exported⟩ := prep_of_spec spec
  have shape := GrowingModule.prepared_shape ix pages
  rw [prepared] at shape
  obtain ⟨rfl, noCode, mems, exports, _, items, child, accept, check, storeFuncs,
    itemsStub, childStub, acceptStub, declared, checkShape⟩ := LoopSound.preparedShape_facts shape
  obtain ⟨code, params, results, codeIs, localTypes, instrs, expanded, paramsLen, resultsLen,
    localFuncs, localMems, defaults⟩ := fnOk_spec checkShape
  have atCheck : cfg.store.funcs[3]? = some check := by rw [storeFuncs]; rfl
  let request := BitVec.ofNat 32 requested.val
  have canInvoke : InvokeOk cfg.store 3 [.i32 root, .i32 request] := by
    have signature := Expand.iff.1 expanded
    rw [declared] at signature
    change some (Ty.func (Ty.ofList [.i32, .i32]) .nil) = some (Ty.func params results) at signature
    obtain ⟨rfl, rfl⟩ := Ty.func.inj (Option.some.inj signature)
    exact ⟨check, _, _, atCheck, expanded, .cons (.num _) (.cons (.num _) .nil)⟩
  have session : TSession profile L (Growing.mod ix pages) (some 0) (listRoles ix ans)
      (cfg.withStart none) initState instance_.addrs .inst false (cfg.withStart none, initState) [] := .start
  have exportedCheck : 3 ∈ instance_.addrs := by rw [← exported, exports]; simp
  have called := session.invoke (by decide) ⟨[], noCode⟩ exportedCheck canInvoke
  have frameEq : Frame.forCall check.module [.i32 root, .i32 request] code.locals =
      locals check.module root request 0 0 := by
    unfold Frame.forCall
    rw [localTypes, defaults]
    rfl
  let noHost : HostSemantics Nat := fun _ _ _ _ => False
  have enterCheck := Step.callRefFunc (P := profile) (host := noHost) (s := cfg.store) (f := {})
    (c := .callRefType ((cfg.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [.i32 root, .i32 request])
    trivial atCheck expanded (by rw [paramsLen]; rfl) codeIs
  rw [frameEq, resultsLen, instrs] at enterCheck
  have allocated := GrowingModule.initial_alloc prepared
  obtain ⟨reached, funcs, space, succeeds⟩ := reserveStore allocated requested allows
  have memoryAt : cfg.store.mem? (locals check.module root request 0 0) ⟨0⟩ = some (0, initialMem pages) :=
    mem?_of localMems (by simp [allocated])
  have reserveRun : Steps profile noHost
      ⟨cfg.store, locals check.module root request 0 0, expression (reserve ++ body)⟩
      ⟨reached, locals check.module root 0 0 0, expression body⟩ :=
    ReserveReplay.steps_of_success rfl (by change 1 < 4; decide) memoryAt rfl
      ((initial_pages pages).trans_le pages.property) succeeds
  have enterLoop : Step profile noHost ⟨reached, locals check.module root 0 0 0, expression body⟩
      ⟨reached, locals check.module root 0 0 0, [.label 0 body (expression iteration)]⟩ :=
    Step.loop (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have inner : Steps profile noHost
      ⟨cfg.store, locals check.module root request 0 0, expression (reserve ++ body)⟩
      ⟨reached, locals check.module root 0 0 0, [.label 0 body (expression iteration)]⟩ :=
    reserveRun.trans enterLoop.steps
  have loop := TSession.of_core_steps called (enterCheck.steps.trans inner.label.frame)
  obtain ⟨stopped, lastState, run⟩ := drive (module_ := Growing.mod ix pages) rfl plan names localFuncs localMems
    itemsStub childStub acceptStub (index := 0) (by simp) (funcs.trans storeFuncs) space loop
  have memoryAddr : (cfg.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, mems]
  refine ⟨.enter none :: (remainingReads root handles handles answerFor).map .inp,
    ⟨mt, instance_, cfg.withStart none, spec, L, initState, env, .run, true, (stopped, lastState), ?_⟩, ?_⟩
  · rw [memoryAddr]
    exact run
  · change .enter :: Silmaril.Wasm.Game.HandleAccept.Memory.inputsOf (some .enter)
      ((remainingReads root handles handles answerFor).map .inp) = _
    rw [input_map]

theorem byte_reply_accepts {profile : Profile} (checker : Checker) (pages requested : InitialPages)
    (allows : pages.val < requested.val →
      profile.growMaySucceed .memory 0 pages.val (requested.val - pages.val))
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)}
    {rho : Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ max pages.val requested.val * 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ max pages.val requested.val * 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs reply) 0 (Growing.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos := by
  let capacity := max pages.val requested.val * 65536
  have pageBound : max pages.val requested.val ≤ 65536 := max_le pages.property requested.property
  have width : capacity ≤ 2 ^ 32 := by
    change max pages.val requested.val * 65536 ≤ 4294967296
    omega
  have names : checker.imports.child ≠ checker.imports.items ∧ checker.imports.accept ≠ checker.imports.items ∧
      checker.imports.accept ≠ checker.imports.child := by cases checker <;> decide
  have valid : (Verify.specInstance? (Growing.mod checker.imports pages)).isSome = true := by
    unfold Verify.specInstance?
    rw [GrowingModule.validate_shape]
    rfl
  obtain ⟨mt, instance_, initial, spec⟩ := Live.spec_exists valid
  have transcript := trace names requested allows spec (GrowingModule.byte_reply_admitted instance_.store handles raw) ()
    (bytes_plan (root := root) checker width fits raw space)
  refine accepts_trace transcript policy allowed rootDenotes denotes ?_
  intro handle member
  obtain ⟨atom, meaning, named⟩ := atoms handle member
  exact ⟨atom, by simp [meaning], named⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingTrace
