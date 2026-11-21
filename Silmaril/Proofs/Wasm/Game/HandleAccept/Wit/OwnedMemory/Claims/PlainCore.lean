module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Lift.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core
  (Contract LocalIssue runLocal childFromHistory decodeChildren)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeArgs requireSome)
open Silmaril.Wasm.Game.Accept (Callout)

private theorem schema (sig : PlainSignature) (tag : sig.val.Tag) :
    checkSchema (sig.val.payload tag) = Stored.checkSchema (sig.val.payload tag) := by
  have admitted := sig.property tag
  unfold Stored.checkSchema at admitted
  split at admitted
  · cases admitted
  · rename_i notBorrow
    split at admitted
    · cases admitted
    · rw [sig.property tag]
      unfold checkSchema
      rwa [ite_eq_right notBorrow]

private theorem root_empty (sig : PlainSignature) (tree : Tree sig.val) : Claims.rootReceipts tree = [] := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag payload _ _ =>
    exact List.map_eq_nil_iff.mp (payload.2.property.2.trans
      (requirements_of_schema (sig.property payload.1) payload.2.val.value))

private theorem endpoints_erase (sig : Stored.Signature) (tree : Tree sig) :
    Claims.rootEndpoints tree = Stored.Endpoints.rootIds tree.erase := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag _ _ _ => rfl

private theorem register (sig : PlainSignature) (state : Stored.Endpoints.State sig.val)
    (tree : Stored.Tree sig.val) :
    Claims.State.register ⟨state.accepted.map (Tree.equivPlain sig), [], state.held⟩
        (Tree.equivPlain sig tree) =
      ((state.register tree).map fun writer =>
        (⟨writer.accepted.map (Tree.equivPlain sig), [], writer.held⟩ : Claims.State sig.val)).mapError
          (fun _ => Claims.Issue.alias) := by
  have sameEndpoints : Claims.rootEndpoints (Tree.equivPlain sig tree) = Stored.Endpoints.rootIds tree := by
    rw [endpoints_erase, ← Tree.equivPlain_symm sig, Equiv.symm_apply_apply]
  unfold Claims.State.register Stored.Endpoints.State.register
  simp [root_empty, sameEndpoints]
  split <;> rfl

private theorem lookupMap {α β : Type} (embed : α → β) (history : List α) (handle : BitVec 32) :
    childFromHistory (history.map embed) handle = (childFromHistory history handle).map embed := by
  unfold childFromHistory
  by_cases valid : 0 < handle.toNat ∧ handle.toNat ≤ history.length
  · simp [guard, valid]
  · simp [guard, valid]

private theorem requireSomeMap {α β Error : Type} (embed : α → β) (issue : Error) (value : Option α) :
    requireSome issue (value.map embed) = embed <$> requireSome issue value := by
  cases value <;> rfl

private theorem childrenMap {α β : Type} (embed : α → β) (observed : Callout)
    (history : List α) (ptr count : Nat) :
    decodeChildren observed (history.map embed) ptr count =
      List.map embed <$> decodeChildren observed history ptr count := by
  unfold decodeChildren
  simp only [map_bind]
  congr 1
  funext bytes
  congr 1
  funext handles
  induction handles with
  | nil => rfl
  | cons handle rest ih =>
    simp only [List.mapM_cons, map_bind]
    rw [ih, lookupMap, requireSomeMap]
    simp only [bind_map_left, map_pure]
    rfl

private theorem preflight (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) (memory : Option Nat) (state : Stored.Endpoints.Core.World grow sig.val)
    (call : UCall Nat) :
    Claims.Core.preflight contract memory (embedWorld sig state) call =
      ((contract.preflight memory state.writer call).map fun result =>
        (result.1, result.2.map (Tree.equivPlain sig))).mapError Claims.Core.Issue.boundary := by
  unfold Claims.Core.preflight Contract.preflight
  split
  · rfl
  · have operands : contract.preflightOperands checkSchema memory
          (state.writer.accepted.map (Tree.equivPlain sig)) call =
        (fun result => (result.1, result.2.map (Tree.equivPlain sig))) <$>
          contract.preflightOperands Stored.checkSchema memory state.writer.accepted call := by
      unfold Contract.preflightOperands
      simp only [List.length_map, schema, childrenMap, bind_map_left, apply_ite, map_bind, map_pure]
    rw [show (embedWorld sig state).writer.accepted = state.writer.accepted.map (Tree.equivPlain sig) from rfl]
    rw [operands]
    rfl

private theorem runLocalMap {E : CoreEngine} {α β : Type} (embed : α → β)
    (program : P E Unit α) (store : CStore E) :
    runLocal (embed <$> program) store = ((runLocal program store).1, (runLocal program store).2.map embed) := by
  induction program generalizing store with
  | pure _ => rfl
  | op op next ih =>
    change runLocal (.op op (fun response => embed <$> next response)) store = _
    cases op with
    | get => exact ih store store
    | modify update => exact ih () (update store)
    | _ => rfl

private theorem load (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) (memory : Option Nat) (state : Stored.Endpoints.Core.World grow sig.val)
    (call : UCall Nat) :
    let old := contract.load memory state call
    let new := Claims.Core.load contract memory (embedWorld sig state) call
    new.1 = old.1 ∧ new.2.mapError oldIssue = (old.2.map (Tree.equivPlain sig)).mapError some := by
  dsimp only
  unfold Claims.Core.load Contract.load
  rw [preflight]
  cases checked : contract.preflight memory state.writer call with
  | error issue => exact ⟨rfl, rfl⟩
  | ok result =>
    obtain ⟨args, children⟩ := result
    dsimp only [Except.map, Except.mapError, embedWorld]
    rw [buildNode_plain, runLocalMap]
    constructor
    · rfl
    · generalize runLocal _ _ = executed
      obtain ⟨store, result⟩ := executed
      cases result with
      | error _ => rfl
      | ok checked => cases checked <;> rfl

theorem attempt (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) (memory : Option Nat) (state : Stored.Endpoints.Core.World grow sig.val)
    (call : UCall Nat) :
    let old := contract.attempt memory state call
    let new := Claims.Core.attempt contract memory (embedWorld sig state) call
    new.1 = embedWorld sig old.1 ∧ new.2.mapError oldIssue = old.2.mapError some := by
  have same := load sig contract memory state call
  dsimp only at same ⊢
  unfold Claims.Core.attempt Contract.attempt
  generalize newLoad : Claims.Core.load contract memory (embedWorld sig state) call = new at same ⊢
  generalize oldLoad : contract.load memory state call = old at same ⊢
  obtain ⟨oldStore, oldResult⟩ := old
  obtain ⟨newStore, newResult⟩ := new
  obtain ⟨sameStore, sameResult⟩ := same
  dsimp only at sameStore sameResult
  subst newStore
  cases oldResult with
  | error oldIssueValue =>
    cases newResult with
    | error _ => exact ⟨rfl, congrArg Except.error (Except.error.inj sameResult)⟩
    | ok _ => cases sameResult
  | ok oldTree =>
    cases newResult with
    | error _ => cases sameResult
    | ok newTree =>
      have tree : newTree = Tree.equivPlain sig oldTree := Except.ok.inj sameResult
      subst newTree
      simp only [Except.bind, embedWorld, register]
      generalize registered : state.writer.register oldTree = result
      cases result with
      | error issue =>
        have onlyAlias : issue = .alias := by
          unfold Stored.Endpoints.State.register at registered
          dsimp only at registered
          split at registered
          · cases registered
          · cases registered
            rfl
        subst issue
        exact ⟨rfl, rfl⟩
      | ok writer =>
        simp [Except.map, Except.mapError, List.length_map]

theorem answer (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) (memory : Option Nat) (state : Stored.Endpoints.Core.World grow sig.val)
    (call : UCall Nat) (reply : UReply) (updated : Claims.Core.World grow sig.val) :
    Claims.Core.answer contract memory (embedWorld sig state) call reply updated ↔
      ∃ old, contract.answer memory state call reply old ∧ updated = embedWorld sig old := by
  have same := attempt sig contract memory state call
  dsimp only at same
  unfold Claims.Core.answer Contract.answer
  generalize Claims.Core.attempt contract memory (embedWorld sig state) call = new at same ⊢
  generalize contract.attempt memory state call = old at same ⊢
  obtain ⟨oldState, oldResult⟩ := old
  obtain ⟨newState, newResult⟩ := new
  obtain ⟨states, results⟩ := same
  dsimp only at states results ⊢
  subst newState
  have agreed (returns : Prop) : (updated = embedWorld sig oldState ∧ returns) ↔
      ∃ old, (old = oldState ∧ returns) ∧ updated = embedWorld sig old :=
    ⟨fun ⟨frame, ret⟩ => ⟨oldState, ⟨rfl, ret⟩, frame⟩,
      fun ⟨_, ⟨frame, ret⟩, eq⟩ => ⟨eq.trans (congrArg (embedWorld sig) frame), ret⟩⟩
  cases oldResult <;> cases newResult
  case error.error => exact agreed _
  case error.ok => cases results
  case ok.error => cases results
  case ok.ok expected actual =>
    have sameHandle : actual = expected := Except.ok.inj results
    subst actual
    exact agreed _

variable {Entry Input Output Exit : Type}

theorem worldInjective (sig : PlainSignature) {grow : SingleThreaded.GrowOracle} :
    Function.Injective (embedWorld sig (grow := grow)) := by
  intro prior next same
  have reference : prior.reference = next.reference := congrArg Claims.Core.World.reference same
  have endpoints : prior.writer.held = next.writer.held := congrArg (·.writer.endpoints) same
  have accepted : prior.writer.accepted = next.writer.accepted :=
    (List.map_injective_iff.mpr (Tree.equivPlain sig).injective) (congrArg (·.writer.accepted) same)
  obtain ⟨priorReference, priorWriter⟩ := prior
  obtain ⟨nextReference, nextWriter⟩ := next
  obtain ⟨priorAccepted, priorHeld⟩ := priorWriter
  obtain ⟨nextAccepted, nextHeld⟩ := nextWriter
  cases reference
  cases endpoints
  cases accepted
  rfl

theorem sessionForward (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) {memory : Option Nat}
    {state : Stored.Endpoints.Core.World grow sig.val} {profile : Numerics.Profile} {module_ : Module}
    {roles : Roles Entry Input Output Exit} {start : Config Nat} {addrs : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × Stored.Endpoints.Core.World grow sig.val}
    {tags : List (Silmaril.Accept.IO.Tag Entry Input Output Exit)}
    (session : TSession profile (contract.env grow memory) module_ memory roles start state addrs
      phase pending current tags) :
    TSession profile (Claims.Core.env contract grow memory) module_ memory roles start (embedWorld sig state)
      addrs phase pending (current.1, embedWorld sig current.2) tags := by
  refine TSession.rec (motive := fun phase pending (current : Config Nat × Stored.Endpoints.Core.World grow sig.val)
    tags _ => TSession profile (Claims.Core.env contract grow memory) module_ memory roles start
      (embedWorld sig state) addrs phase pending (current.1, embedWorld sig current.2) tags)
    ?base ?internal ?call ?answer ?invoke ?ret session
  case base => exact .start
  case internal => intro _ _ _ _ _ _ _ step ih; exact .internal ih step
  case call => intro _ _ _ _ _ _ _ _ _ redex ih; exact .call ih redex
  case answer =>
    intro _ config prior next _ _ _ target args reply _ redex answered ih
    exact .answer ih redex ((answer sig contract memory prior ⟨target, config.store, args⟩ reply
      (embedWorld sig next)).2 ⟨next, answered, rfl⟩)
  case invoke => intro _ _ _ _ _ _ _ _ phase finished exported valid ih; exact .invoke ih phase finished exported valid
  case ret => intro _ _ _ _ _ _ done ih; exact .ret ih done

theorem sessionBackward (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) {memory : Option Nat}
    {state : Stored.Endpoints.Core.World grow sig.val} {profile : Numerics.Profile} {module_ : Module}
    {roles : Roles Entry Input Output Exit} {start : Config Nat} {addrs : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × Claims.Core.World grow sig.val}
    {tags : List (Silmaril.Accept.IO.Tag Entry Input Output Exit)}
    (session : TSession profile (Claims.Core.env contract grow memory) module_ memory roles start
      (embedWorld sig state) addrs phase pending current tags) :
    ∃ old, current.2 = embedWorld sig old ∧
      TSession profile (contract.env grow memory) module_ memory roles start state addrs
        phase pending (current.1, old) tags := by
  refine TSession.rec (motive := fun phase pending (current : Config Nat × Claims.Core.World grow sig.val)
    tags _ => ∃ old, current.2 = embedWorld sig old ∧
      TSession profile (contract.env grow memory) module_ memory roles start state addrs
        phase pending (current.1, old) tags)
    ?base ?internal ?call ?answer ?invoke ?ret session
  case base => exact ⟨state, rfl, .start⟩
  case internal =>
    intro _ _ _ _ _ _ _ step ih
    obtain ⟨old, frame, run⟩ := ih
    exact ⟨old, frame, .internal run step⟩
  case call =>
    intro _ _ _ _ _ _ _ _ _ redex ih
    obtain ⟨old, frame, run⟩ := ih
    exact ⟨old, frame, .call run redex⟩
  case answer =>
    intro _ config prior next _ _ _ target args reply _ redex answered ih
    obtain ⟨old, frame, run⟩ := ih
    have typed : Claims.Core.answer contract memory prior ⟨target, config.store, args⟩ reply next := answered
    rw [show prior = embedWorld sig old from frame] at typed
    obtain ⟨updated, oldReply, updates⟩ := (answer sig contract memory ..).1 typed
    exact ⟨updated, updates, .answer run redex oldReply⟩
  case invoke =>
    intro _ _ _ _ _ _ _ _ phase finished exported valid ih
    obtain ⟨old, frame, run⟩ := ih
    exact ⟨old, frame, .invoke run phase finished exported valid⟩
  case ret =>
    intro _ _ _ _ _ _ done ih
    obtain ⟨old, frame, run⟩ := ih
    exact ⟨old, frame, .ret run done⟩

theorem sessionIff (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) {memory : Option Nat}
    {state : Stored.Endpoints.Core.World grow sig.val} {profile : Numerics.Profile} {module_ : Module}
    {roles : Roles Entry Input Output Exit} {start : Config Nat} {addrs : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × Stored.Endpoints.Core.World grow sig.val}
    {tags : List (Silmaril.Accept.IO.Tag Entry Input Output Exit)} :
    TSession profile (Claims.Core.env contract grow memory) module_ memory roles start (embedWorld sig state)
      addrs phase pending (current.1, embedWorld sig current.2) tags ↔
    TSession profile (contract.env grow memory) module_ memory roles start state addrs
      phase pending current tags := by
  constructor
  · intro session
    obtain ⟨prior, frame, run⟩ := sessionBackward sig contract session
    cases worldInjective sig frame
    exact run
  · exact sessionForward sig contract

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore
