module

public import Silmaril.Wasm.Execution.Core.Entry.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms
public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Execution.Core.Soundness
import Silmaril.Wasm.Behaviour.Refinement.Interpreter
import Silmaril.Wasm.Game.Machine.Thms

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Entry

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Semantics.Operational Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement
  Silmaril.Games.Abstract Silmaril.Wasm.Abstract.InstSession Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type} {P : Profile} {host : HostSemantics H} {types : List CValType}

theorem ordinary_may {source : Config H} {outcome : Outcome Completion} :
    (ordinary P host).May source outcome ↔ ∃ final result, Finishes P host source final result ∧
      observeResult result = outcome :=
  ⟨fun ⟨final, run, result, code, observed⟩ => ⟨final, result, ⟨run, code⟩, observed⟩,
   fun ⟨final, result, ⟨run, code⟩, observed⟩ => ⟨final, run, result, code, observed⟩⟩

theorem policy_safe_and_may {source : Config H}
    (preserves : ∀ ⦃left right : Config H⦄, ConfigOk left types → Step P host left right → ConfigOk right types)
    (typed : ConfigOk source types) :
    (policy P host types).SafeAt source ∧
      ∀ outcome, (policy P host types).toOpSem.May source outcome ↔ (ordinary P host).May source outcome := by
  have allTyped : ∀ ⦃target⦄, (ordinary P host).Reach source target → ConfigOk target types := by
    intro target run
    induction run with
    | refl => exact typed
    | tail _ step ih => exact preserves ih step
  exact ⟨WithUB.enforce_safe_iff.mpr ⟨WithUB.ofOpSem_safe _ _, allTyped⟩,
    fun _ => WithUB.enforce_may_iff allTyped⟩

theorem noHost_preserves {left right : Config H} (typed : ConfigOk left types) (step : Step P noHost left right) :
    ConfigOk right types := by
  let divergent : HostSemantics H := fun _ _ _ outcome => outcome = .diverged
  have hostOk : HostOk divergent := by
    intro store entry func args params results _ _ _ _ _
    exact ⟨⟨.diverged, rfl⟩, fun outcome equal => by cases equal; trivial⟩
  exact (Step.preservation hostOk typed (step.of_noHost divergent)).1

theorem typedModule_lift {interface : CModuleType} {input : TypedModuleInput H interface} {source : Config H}
    (hostOk : HostOk host) : (rawModule P host).initial input.erase source ↔
      ∃ state, (typedModule P host interface).initial input state ∧ state.val = source := by
  constructor
  · intro init
    exact ⟨⟨source, Instantiate.ok hostOk input.storeOk init⟩, init, rfl⟩
  · rintro ⟨state, init, rfl⟩
    exact init

theorem typedModule_may {interface : CModuleType} (hostOk : HostOk host)
    (source : { state : Config H // ConfigOk state [] }) (outcome : Outcome Completion) :
    ((typedModule P host interface).semantics.toOpSem.May source outcome) ↔
      ∃ final result, Finishes P host source.val final result ∧ observeResult result = outcome := by
  have closed : ∀ ⦃left right⦄, ConfigOk left [] → (policy P host []).step left right → ConfigOk right [] :=
    fun {_ _} typed step => (Step.preservation hostOk typed step.2).1
  exact (WithUB.restrict_may_iff closed source).trans
    (((policy_safe_and_may (P := P) (host := host)
      (fun {_ _} typed step => (Step.preservation hostOk typed step).1) source.property).2 outcome).trans
      ordinary_may)

theorem finishes_unique {oracle : GrowOracle} {source first second : Config H} {one two : Result}
    (left : Finishes (profile oracle) noHost source first one)
    (right : Finishes (profile oracle) noHost source second two) : first = second ∧ one = two := by
  have equal := eq_of_steps_of_nf left.1 right.1
    (fun _ => not_step_of_terminal ⟨one, left.2⟩) (fun _ => not_step_of_terminal ⟨two, right.2⟩)
  subst second
  have code := congrArg codeOutcome? (left.2.symm.trans right.2)
  rw [codeOutcome?_toAdmin, codeOutcome?_toAdmin] at code
  exact ⟨rfl, Option.some.inj code⟩

variable {context : Context} {world : World H context} {parameters results : List IntType}
  {call : DirectCall world parameters results} {oracle : GrowOracle}

theorem invoke_typed (call : DirectCall world parameters results) (args : Values parameters) :
    ConfigOk (invoke world.store call.address args.erase) (stackTypes results) := by
  have accepts := (call.invokeOk_iff args.erase).mpr ⟨args, rfl⟩
  obtain ⟨entry, _, _, found, signature, typed⟩ := invoke_ok world.storeOk accepts
  cases Option.some.inj (call.resolveAddress.symm.trans found)
  cases Expand.func_eq signature call.signature
  simpa only [Ty.toList_ofList] using typed

theorem invoke_finishes_iff (call : DirectCall world parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    {final : Config H} {result : Result} :
    Finishes (profile oracle) noHost (invoke world.store call.address args.erase) final result ↔
      final = ⟨world.store, {}, (invokeResult answer).toAdmin⟩ ∧ result = invokeResult answer := by
  have observed : Finishes (profile oracle) noHost (invoke world.store call.address args.erase)
      ⟨world.store, {}, (invokeResult answer).toAdmin⟩ (invokeResult answer) :=
    ⟨by cases answer <;> exact call.invoke_sound args fuel ran, rfl⟩
  exact ⟨fun other => finishes_unique other observed, fun ⟨configEq, resultEq⟩ => by
    rw [configEq, resultEq]; exact observed⟩

theorem invoke_may_iff (call : DirectCall world parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (policy (profile oracle) noHost (stackTypes results)).toOpSem.May
      (invoke world.store call.address args.erase) outcome ↔ outcome = observeResult (invokeResult answer) := by
  rw [(policy_safe_and_may (P := profile oracle) (host := noHost)
    (fun {_ _} => noHost_preserves) (invoke_typed call args)).2 outcome, ordinary_may]
  constructor
  · rintro ⟨final, result, run, rfl⟩
    rw [((invoke_finishes_iff call args ran).mp run).2]
  · rintro rfl
    exact ⟨_, _, (invoke_finishes_iff call args ran).mpr ⟨rfl, rfl⟩, rfl⟩

theorem typed_invoke_may_iff (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (typedSem.toOpSem.May (call.start args) outcome) ↔
      (policy (profile oracle) noHost (stackTypes results)).toOpSem.May
        (invoke world.store call.address args.erase) outcome := by
  have result : ((call.start args).runFor fuel).result? = some (invokeResult answer) := by
    unfold State.result?
    rw [show ((call.start args).runFor fuel).control.result? = some answer from ran]
    cases answer <;> rfl
  have reaches := ((call.start args).typedReach_iff _).mpr ⟨fuel, rfl⟩
  have observed : typedSem.toOpSem.May (call.start args) (observeResult (invokeResult answer)) :=
    ⟨_, reaches, _, result, rfl⟩
  rw [invoke_may_iff call args ran outcome]
  constructor
  · intro may
    have raw := ((call.start args).may_iff (oracle := oracle) outcome).mpr may
    have rawObserved := ((call.start args).may_iff (oracle := oracle) _).mpr observed
    have readback (outcome : Outcome Completion)
        (may : (rawSem oracle (stackTypes results)).toOpSem.May (call.start args).erase outcome) :=
      ordinary_may.mp ((policy_safe_and_may (P := profile oracle) (host := noHost)
        (fun {_ _} => noHost_preserves) (call.start args).sound).2 outcome |>.mp may)
    obtain ⟨_, _, left, rfl⟩ := readback outcome raw
    obtain ⟨_, _, right, equal⟩ := readback _ rawObserved
    exact (congrArg observeResult (finishes_unique left right).2).trans equal
  · rintro rfl
    exact observed

theorem typedInstance_may_iff {registered : ScalarInstance} {readyWorld : World Nat context}
    (call : DirectCall readyWorld parameters results) (wellFormed : registered.WellFormed readyWorld.store)
    (args : Values parameters) (question : registered.F.Op)
    (address : registered.addr question.1 = call.address) (arguments : question.2.val = args.erase)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (typedInstance registered call wellFormed).semantics.toOpSem.May (call.start args) outcome ↔
      (scalarInstance oracle registered (stackTypes results)).semantics.toOpSem.May
        ((registered.initThread question).config readyWorld.store) outcome := by
  change typedSem.toOpSem.May (call.start args) outcome ↔
    (policy (profile oracle) noHost (stackTypes results)).toOpSem.May
      (invoke readyWorld.store (registered.addr question.1) question.2.val) outcome
  rw [address, arguments]
  exact typed_invoke_may_iff args ran outcome

theorem session_finishes_iff {registered : ScalarInstance} {readyWorld : World Nat context}
    (call : DirectCall readyWorld parameters results)
    (args : Values parameters) {question : registered.F.Op} (closed : registered.imports = [])
    (address : registered.addr question.1 = call.address) (arguments : question.2.val = args.erase)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    {typedAnswer : registered.F.Ar question}
    (readback : Answer.ofResult? (registered.exports.get question.1) (invokeResult answer) = some typedAnswer)
    (log : List (Call registered.E)) (ending : End (Store Nat) (Res registered.exports ⊕ PUnit)) :
    (log, ending) ∈ instFinS registered (profile oracle) readyWorld.store question ↔
      ending = .ret (sAns question typedAnswer) readyWorld.store := by
  have noLog : log = [] := by
    cases log with
    | nil => rfl
    | cons first _ =>
      have impossible : first.1.1.val < 0 := by simpa [closed] using first.1.1.isLt
      exact (Nat.not_lt_zero _ impossible).elim
  subst log
  have entry : (registered.initThread question).config readyWorld.store =
      invoke readyWorld.store call.address args.erase := by
    change invoke readyWorld.store (registered.addr question.1) question.2.val = _
    rw [address, arguments]
  have finite : Finishes (profile oracle) noHost (invoke readyWorld.store call.address args.erase)
      ⟨readyWorld.store, {}, (invokeResult answer).toAdmin⟩ (invokeResult answer) :=
    (invoke_finishes_iff call args ran).mpr ⟨rfl, rfl⟩
  constructor
  · rintro (⟨other, finalStore, rfl, moves⟩ | ⟨rfl, nextStore, next, moves, diverges⟩)
    · change registered.Path _ _ [.inr (.ask question), .inr (.ans question other)] _ at moves
      cases moves with
      | cons asks afterAsk =>
        cases asks
        cases afterAsk with
        | cons answers stop =>
          cases stop
          cases answers with
          | oret run reached readOther =>
            have actual := Reach.steps (host := noHost) run
            rw [entry] at actual
            obtain ⟨sameConfig, sameResult⟩ := finishes_unique ⟨actual, reached⟩ finite
            have sameStore : finalStore = readyWorld.store := by
              simpa only [Thread.config_store] using congrArg Config.store sameConfig
            rw [sameResult, readback] at readOther
            rw [sameStore, Option.some.inj readOther]
    · change registered.Path _ _ [.inr (.ask question)] _ at moves
      cases moves with
      | cons asks stop =>
        cases asks
        cases stop
        exfalso
        apply call.invoke_not_diverges args (oracle := oracle) ran
        obtain ⟨trace, first, adjacent⟩ := diverges
        refine ⟨fun index => (trace index).2.config (trace index).1, ?_, ?_⟩
        · change (trace 0).2.config (trace 0).1 = _
          rw [first, entry]
        · intro index
          obtain ⟨frame, code, active, actual⟩ := adjacent index
          change Step _ _ ((trace index).2.config (trace index).1)
            ((trace (index + 1)).2.config (trace (index + 1)).1)
          rw [active]
          exact actual
  · rintro rfl
    obtain ⟨finalStore, thread, run, reached⟩ := (ret_iff_core (r := invokeResult answer)).mpr
      ⟨_, entry.symm ▸ finite.1, finite.2⟩
    have actual := Reach.steps (host := noHost) run
    rw [entry] at actual
    have sameStore : finalStore = readyWorld.store := by
      simpa only [Thread.config_store] using
        congrArg Config.store (finishes_unique ⟨actual, reached⟩ finite).1
    subst finalStore
    exact Or.inl ⟨typedAnswer, _, rfl, .cons (.call _ _) (.cons (.oret run reached readback) (.nil _))⟩

end Silmaril.Proofs.Wasm.Execution.Core.Entry
