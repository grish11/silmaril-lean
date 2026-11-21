module

public import Silmaril.Wasm.Execution.Core.MemoryProfile.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Semantics.Operational.Policy.Thms
import Silmaril.Wasm.Execution.Core.Soundness

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.MemoryProfile

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.MemoryProfile
  Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement Silmaril.Semantics.Operational

variable {oracle : GrowOracle} {height input output : Nat}

private theorem zero_effAddr (address : Nat) : effAddr address memarg0 = address := Nat.add_zero address

private theorem mem_lookup (bytes : ByteArray) :
    (world bytes).mem? frame index = some (0, memory bytes) := rfl

private theorem valid_load_redex (bytes : ByteArray) (address bits : BitVec 32)
    (reads : Memory.load bytes address.toNat 4 = some bits) :
    MemoryStep (profile oracle) (config bytes (vals [word address] ++ [load]))
      (config bytes [(word bits).toAdmin]) := by
  have reads' : Memory.load bytes (effAddr address.toNat memarg0) 4 = some bits := by
    rwa [zero_effAddr]
  have head := MemoryStep.loadIntVal (P := profile oracle) (a := .i32) (t := .i32) (arg := memarg0)
    (i := address) (c := bits) (mem_lookup bytes) reads'
  change MemoryStep (profile oracle) _ (config bytes [(word (bits.setWidth 32)).toAdmin]) at head
  rwa [BitVec.setWidth_eq] at head

private theorem invalid_load_redex (bytes : ByteArray) (address : BitVec 32)
    (reads : Memory.load bytes address.toNat 4 = none) :
    MemoryStep (profile oracle) (config bytes (vals [word address] ++ [load])) (config bytes [.trap]) := by
  have oob : bytes.size < address.toNat + 4 := by
    by_contra! bound
    simp [Memory.load, Memory.readBytes, bound] at reads
  have oob' : bytes.size < effAddr address.toNat memarg0 + 4 := by rwa [zero_effAddr]
  exact MemoryStep.loadIntOob (a := .i32) (t := .i32) (mem_lookup bytes) oob'

private theorem valid_store_redex (bytes after : ByteArray) (address bits : BitVec 32)
    (writes : Memory.store bytes address.toNat (count := 4) bits = some after) :
    MemoryStep (profile oracle) (config bytes (vals [word address, word bits] ++ [store]))
      (config after []) := by
  apply MemoryStep.storeIntVal (a := .i32) (t := .i32) (mem_lookup bytes)
  change Memory.store bytes (effAddr address.toNat memarg0) (count := 4) (bits.setWidth 32) = some after
  rwa [zero_effAddr, BitVec.setWidth_eq]

private theorem invalid_store_redex (bytes : ByteArray) (address bits : BitVec 32)
    (writes : Memory.store bytes address.toNat (count := 4) bits = none) :
    MemoryStep (profile oracle) (config bytes (vals [word address, word bits] ++ [store]))
      (config bytes [.trap]) := by
  have oob : bytes.size < address.toNat + 4 := by
    by_contra! bound
    simp [Memory.store, Memory.writeBytes, bound] at writes
  have oob' : bytes.size < effAddr address.toNat memarg0 + 4 := by rwa [zero_effAddr]
  exact MemoryStep.storeIntOob (a := .i32) (t := .i32) (mem_lookup bytes) oob'

private theorem add_head (bytes : ByteArray) (left right : BitVec 32) :
    Head (profile oracle) (world bytes) frame [word left, word right] add
      (config bytes [(word (left + right)).toAdmin]) :=
  .numeric (NumericStep.intBinOp (t := .i32) (op := .add) rfl)

private theorem active_eq {bytes : ByteArray} {saved arguments : List Val} {inst : Admin}
    {rest : List Admin} {head target : Config Unit} (hc : famOf inst ≠ .control)
    (hs : Head (profile oracle) (world bytes) frame arguments inst head)
    (step : Step (profile oracle) noHost (config bytes (vals saved ++ (vals arguments ++ inst :: rest))) target) :
    target = ⟨head.store, head.frame, vals saved ++ head.code ++ rest⟩ := by
  have known : HeadDec (profile oracle) (world bytes) frame
      (vals saved ++ (vals arguments ++ inst :: rest))
      ⟨head.store, head.frame, vals saved ++ head.code ++ rest⟩ :=
    ⟨saved, arguments, inst, rest, head, rfl, hs, rfl⟩
  rcases Det.Step.decomp step with other | bubble
  · obtain ⟨p, args, op, suffix, after, front, -, headStep, rfl⟩ := fnv_headDec other
    have canonical : fnv (vals saved ++ (vals arguments ++ inst :: rest)) =
        (saved ++ arguments, inst :: rest) := by
      simp [fnv_cons_of_none hs.good.val_none]
    change fnv (vals saved ++ (vals arguments ++ inst :: rest)) = (p ++ args, op :: suffix) at front
    rw [canonical] at front
    simp only [Prod.mk.injEq, List.cons.injEq] at front
    obtain ⟨shape, rfl, rfl⟩ := front
    rcases append_eq_append_suffix shape with ⟨extra, equal⟩ | ⟨extra, equal⟩
    · obtain ⟨rfl, same⟩ := Head.det_fam hc hs headStep equal
      simp only [List.nil_append] at equal
      subst args after
      rw [List.append_cancel_right shape]
    · obtain ⟨rfl, same⟩ := Head.det_fam hc headStep hs equal
      simp only [List.nil_append] at equal
      subst args after
      rw [List.append_cancel_right shape]
  · exact (headDec_bubble_false known bubble).elim

private theorem active_iff {bytes : ByteArray} {saved arguments : List Val} {inst : Admin}
    {rest : List Admin} {head target : Config Unit} (hc : famOf inst ≠ .control)
    (hs : Head (profile oracle) (world bytes) frame arguments inst head)
    (redex : Step (profile oracle) noHost (config bytes (vals arguments ++ [inst])) head) :
    Step (profile oracle) noHost (config bytes (vals saved ++ (vals arguments ++ inst :: rest))) target ↔
      target = ⟨head.store, head.frame, vals saved ++ head.code ++ rest⟩ := by
  refine ⟨active_eq hc hs, ?_⟩
  rintro rfl
  simpa [config, List.append_assoc] using lift_instrs saved rest _ _ redex

theorem load_step_iff (bytes : ByteArray) (address : BitVec 32) (saved : List Val) (rest : List Admin)
    (target : Config Unit) :
    Step (profile oracle) noHost (config bytes (vals saved ++ ((word address).toAdmin :: load :: rest))) target ↔
      target = config bytes (vals saved ++
        (match Memory.load bytes address.toNat 4 with
        | none => [.trap]
        | some bits => [(word bits).toAdmin]) ++ rest) := by
  cases reads : Memory.load bytes address.toNat 4 with
  | none =>
    have redex := invalid_load_redex (oracle := oracle) bytes address reads
    exact active_iff (arguments := [word address]) (inst := load) (by decide) (.memory redex) (.memory redex)
  | some bits =>
    have redex := valid_load_redex (oracle := oracle) bytes address bits reads
    exact active_iff (arguments := [word address]) (inst := load) (by decide) (.memory redex) (.memory redex)

theorem store_step_iff (bytes : ByteArray) (address bits : BitVec 32) (saved : List Val)
    (rest : List Admin) (target : Config Unit) :
    Step (profile oracle) noHost (config bytes (vals saved ++
      ((word address).toAdmin :: (word bits).toAdmin :: store :: rest))) target ↔
      target = match Memory.store bytes address.toNat (count := 4) bits with
        | none => config bytes (vals saved ++ [.trap] ++ rest)
        | some after => config after (vals saved ++ rest) := by
  cases writes : Memory.store bytes address.toNat (count := 4) bits with
  | none =>
    have redex := invalid_store_redex (oracle := oracle) bytes address bits writes
    exact active_iff (arguments := [word address, word bits]) (inst := store)
      (by decide) (.memory redex) (.memory redex)
  | some after =>
    have redex := valid_store_redex (oracle := oracle) bytes after address bits writes
    simpa [config, vals] using active_iff (saved := saved) (rest := rest) (target := target)
      (arguments := [word address, word bits]) (inst := store) (by decide) (.memory redex) (.memory redex)

private theorem stack_allowed (stack : Stack input) : ∀ inst ∈ vals stack.values, Allowed inst := by
  induction stack with
  | nil => simp [Stack.values, vals]
  | push bits stack ih =>
    intro inst member
    change inst ∈ vals (stack.values ++ [word bits]) at member
    rw [vals_append] at member
    change inst ∈ vals stack.values ++ [(word bits).toAdmin] at member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ih inst member
    · exact .word bits

private theorem code_allowed (code : Code input output) : ∀ inst ∈ code.erase, Allowed inst := by
  induction code <;> simp only [Code.erase, List.mem_cons] <;> intro inst member
  · cases member
  all_goals
    rcases member with rfl | member
    · first | exact .word _ | exact .add | exact .load | exact .store
    · exact (by assumption : ∀ op ∈ _, Allowed op) inst member

private theorem flat_config {bytes : ByteArray} {code : List Admin}
    (allowed : ∀ inst ∈ code, Allowed inst) : InProfile (config bytes code) :=
  ⟨⟨bytes, rfl⟩, rfl, allowed⟩

private theorem start_profile (code : Code input output) (stack : Stack input) (bytes : ByteArray) :
    InProfile (code.start stack bytes) := by
  apply flat_config
  intro inst member
  rcases List.mem_append.mp member with member | member
  · exact stack_allowed stack inst member
  · exact code_allowed code inst member

private def Pending (state : Config Unit) : Prop := InProfile state ∧
  ∃ bytes saved rest, state = config bytes (vals saved ++ .trap :: rest)

private theorem pending (stack : Stack input) (code : Code height output) (bytes : ByteArray) :
    Pending (config bytes (vals stack.values ++ .trap :: code.erase)) := by
  refine ⟨flat_config ?_, bytes, stack.values, code.erase, rfl⟩
  intro inst member
  rcases List.mem_append.mp member with member | member
  · exact stack_allowed stack inst member
  · rcases List.mem_cons.mp member with rfl | member
    · exact .trap
    · exact code_allowed code inst member

private theorem pending_closed {source target : Config Unit} (prior : Pending source)
    (edge : Step (profile oracle) noHost source target) : Pending target := by
  obtain ⟨⟨_, _, allowed⟩, bytes, saved, rest, rfl⟩ := prior
  have front : fnv (config bytes (vals saved ++ Admin.trap :: rest)).code =
      (saved, Admin.trap :: rest) := by simp [config]
  rcases Det.Step.decomp edge with head | bubble
  · obtain ⟨_, _, inst, _, _, first, _, head, _⟩ := fnv_headDec head
    rw [front] at first
    have same : inst = .trap := (List.cons.inj (congrArg Prod.snd first)).1.symm
    exact (head.good.ne_trap same).elim
  · obtain ⟨keep, discard, skipped, tail, _, ⟨first, _, rfl⟩ | ⟨_, first, _, _⟩⟩ := fnv_bubble bubble
    · rw [front] at first
      have savedEq : saved = keep ++ discard := congrArg Prod.fst first
      have restEq := (List.cons.inj (congrArg Prod.snd first)).2
      have allowed' : ∀ inst ∈ vals keep ++ .trap :: tail, Allowed inst := by
        intro inst member
        apply allowed inst
        change inst ∈ vals saved ++ .trap :: rest
        rw [savedEq, restEq, vals_append]
        simp only [List.mem_append, List.mem_cons] at member ⊢
        tauto
      simpa only [config, List.append_assoc, List.singleton_append] using
        (show Pending (config bytes (vals keep ++ .trap :: tail)) from
          ⟨flat_config allowed', bytes, keep, tail, rfl⟩)
    · rw [front] at first
      cases (List.cons.inj (congrArg Prod.snd first)).1

private theorem pending_trace {source : Config Unit} (prior : Pending source) :
    ∀ ⦃target⦄, Steps (profile oracle) noHost source target → InProfile target := by
  intro target path
  have maintained : Pending target := by
    induction path with
    | refl => exact prior
    | tail _ edge ih => exact pending_closed ih edge
  exact maintained.1

private theorem bubble_to_trap (bytes : ByteArray) (saved : List Val) (rest : List Admin) :
    Steps (profile oracle) noHost (config bytes (vals saved ++ .trap :: rest)) (config bytes [.trap]) := by
  have edge := bubble_to (o := oracle) (s := world bytes) (f := frame) (p := saved) (r := rest)
    (X := [.trap]) (Or.inl rfl)
  have lifted := Relation.reflGen_le_reflTransGen _ _ edge
  change Steps (profile oracle) noHost (config bytes (vals saved ++ [.trap] ++ rest)) (config bytes [.trap]) at lifted
  simpa only [List.append_assoc, List.singleton_append] using lifted

private def Trace (oracle : GrowOracle) (source target : Config Unit) : Prop :=
  Steps (profile oracle) noHost source target ∧
    ∀ ⦃middle⦄, Steps (profile oracle) noHost source middle → InProfile middle

private theorem Trace.prepend {source middle target : Config Unit} (initial : InProfile source)
    (edge : ∀ next, Step (profile oracle) noHost source next ↔ next = middle)
    (tail : Trace oracle middle target) : Trace oracle source target := by
  refine ⟨.head ((edge middle).mpr rfl) tail.1, ?_⟩
  intro reached path
  rcases path.cases_head with rfl | ⟨_, step, rest⟩
  · exact initial
  · exact tail.2 (((edge _).mp step) ▸ rest)

private theorem eval_trace (code : Code input output) (stack : Stack input) (bytes : ByteArray) :
    Trace oracle (code.start stack bytes) (code.eval stack bytes).erase := by
  induction code generalizing bytes with
  | done =>
    refine ⟨by simp [Code.start, Code.erase, Code.eval, Answer.erase, Result.toAdmin]; exact .refl, ?_⟩
    intro target path
    rcases path.cases_head with rfl | ⟨_, edge, _⟩
    · exact start_profile .done stack bytes
    · exact (not_step_of_terminal ⟨.values stack.values, by simp [Code.start, Code.erase, Result.toAdmin, config]⟩ edge).elim
  | const bits tail ih =>
    simpa [Code.eval, Code.start, Code.erase, Stack.values, vals, List.append_assoc] using
      ih (.push bits stack) bytes
  | add tail ih =>
    cases stack
    rename_i right prior
    cases prior
    rename_i left stack
    apply Trace.prepend (start_profile _ _ _) _ (ih (.push (left + right) stack) bytes)
    intro next
    have hs := add_head (oracle := oracle) bytes left right
    have redex : Step (profile oracle) noHost (config bytes (vals [word left, word right] ++ [add]))
        (config bytes [(word (left + right)).toAdmin]) := .numeric (NumericStep.intBinOp rfl)
    simpa [Code.start, Code.erase, Stack.values, vals, config, List.append_assoc] using
      active_iff (saved := stack.values) (rest := tail.erase) (target := next) (by decide) hs redex
  | load tail ih =>
    cases stack
    rename_i address stack
    cases reads : Memory.load bytes address.toNat 4 with
    | none =>
      simp only [Code.eval, reads, Answer.erase, Result.toAdmin]
      apply Trace.prepend (start_profile _ _ _) _
        ⟨bubble_to_trap bytes stack.values tail.erase, pending_trace (pending stack tail bytes)⟩
      intro next
      simpa [Code.start, Code.erase, Stack.values, vals, List.append_assoc, reads] using
        load_step_iff (oracle := oracle) bytes address stack.values tail.erase next
    | some bits =>
      simp only [Code.eval, reads]
      apply Trace.prepend (start_profile _ _ _) _ (ih (.push bits stack) bytes)
      intro next
      simpa [Code.start, Code.erase, Stack.values, vals, List.append_assoc, reads] using
        load_step_iff (oracle := oracle) bytes address stack.values tail.erase next
  | store tail ih =>
    cases stack
    rename_i bits prior
    cases prior
    rename_i address stack
    cases writes : Memory.store bytes address.toNat (count := 4) bits with
    | none =>
      simp only [Code.eval, writes, Answer.erase, Result.toAdmin]
      apply Trace.prepend (start_profile _ _ _) _
        ⟨bubble_to_trap bytes stack.values tail.erase, pending_trace (pending stack tail bytes)⟩
      intro next
      simpa [Code.start, Code.erase, Stack.values, vals, List.append_assoc, writes] using
        store_step_iff (oracle := oracle) bytes address bits stack.values tail.erase next
    | some after =>
      simp only [Code.eval, writes]
      apply Trace.prepend (start_profile _ _ _) _ (ih stack after)
      intro next
      simpa [Code.start, Code.erase, Stack.values, vals, List.append_assoc, writes] using
        store_step_iff (oracle := oracle) bytes address bits stack.values tail.erase next

theorem raw_prefix_admitted (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) {target : Config Unit}
    (path : Steps (profile oracle) noHost (code.start stack bytes) target) : Admitted output target := by
  refine ⟨?_, (eval_trace code stack bytes).2 path⟩
  let divergentHost : HostSemantics Unit := fun _ _ _ outcome => outcome = .diverged
  have hostOk : HostOk divergentHost := by
    intro store entry func args params returns _ _ _ _ _
    exact ⟨⟨.diverged, rfl⟩, fun outcome equal => by cases equal; trivial⟩
  have widened : Steps (profile oracle) divergentHost (code.start stack bytes) target :=
    Relation.ReflTransGen.mono (fun _ _ edge => Step.of_noHost divergentHost edge) _ _ path
  exact (Steps.safe hostOk typed widened).1

theorem normal_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (target : Config Unit) :
    (Steps (profile oracle) noHost (code.start stack bytes) target ∧
      ∀ next, ¬ Step (profile oracle) noHost target next) ↔
      target = (code.eval stack bytes).erase := by
  have run := (eval_trace (oracle := oracle) code stack bytes).1
  have stopped : ∀ next, ¬ Step (profile oracle) noHost (code.eval stack bytes).erase next :=
    fun _ => not_step_of_terminal ⟨_, rfl⟩
  exact ⟨fun ⟨path, normal⟩ => eq_of_steps_of_nf path run normal stopped,
    fun same => same.symm ▸ ⟨run, stopped⟩⟩

theorem safe (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) :
    (semantics oracle output).SafeAt (code.start stack bytes) :=
  WithUB.enforce_safe_iff.mpr ⟨WithUB.ofOpSem_safe _ _, fun {_} path => raw_prefix_admitted code stack bytes typed path⟩

theorem may_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) (outcome : Outcome Intrinsic.Completion) :
    (semantics oracle output).toOpSem.May (code.start stack bytes) outcome ↔
      outcome = Intrinsic.observeResult (code.eval stack bytes).result := by
  refine (WithUB.enforce_may_iff (sem := WithUB.ofOpSem (Intrinsic.rawOrdinary oracle))
    (fun {_} path => raw_prefix_admitted code stack bytes typed path)).trans ?_
  change (∃ target, Steps (profile oracle) noHost (code.start stack bytes) target ∧
    ∃ result, target.code = result.toAdmin ∧ Intrinsic.observeResult result = outcome) ↔ _
  constructor
  · rintro ⟨target, path, result, resultCode, rfl⟩
    have same := (normal_iff code stack bytes target).mp
      ⟨path, fun _ => not_step_of_terminal ⟨result, resultCode⟩⟩
    subst target
    exact congrArg Intrinsic.observeResult (Option.some.inj
      ((outcome?_eq_some_of_code resultCode).symm.trans (outcome?_eq_some_of_code rfl)))
  · rintro rfl
    exact ⟨_, (eval_trace (oracle := oracle) code stack bytes).1, _, rfl, rfl⟩

theorem reach_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) (target : Config Unit) :
    (semantics oracle output).toOpSem.Reach (code.start stack bytes) target ↔
      Steps (profile oracle) noHost (code.start stack bytes) target := by
  constructor
  · exact Relation.ReflTransGen.mono (fun _ _ edge => edge.2) _ _
  · intro path
    induction path with
    | refl => exact .refl
    | tail prior edge ih => exact ih.tail ⟨raw_prefix_admitted code stack bytes typed prior, edge⟩

theorem not_diverges (code : Code input output) (stack : Stack input) (bytes : ByteArray) :
    ¬ Diverges (profile oracle) noHost (code.start stack bytes) :=
  Intrinsic.noHost_not_diverges_of_normal_form (eval_trace code stack bytes).1
    (fun _ => not_step_of_terminal ⟨_, rfl⟩)

theorem config_typed {bytes : ByteArray} {code : List Admin} {types : List CValType}
    (page : bytes.size = Memory.pageSize)
    (instructions : AdminsOk (world bytes) context code (.plain [] types)) :
    ConfigOk (config bytes code) types := by
  have memoryOk : MemInstOk (memory bytes) := by
    refine ⟨(show memoryType.Valid by decide), ?_⟩
    change bytes.size = 1 * Memory.pageSize
    simpa using page
  have storeOk : StoreOk (world bytes) := by
    constructor <;> simp [world, memoryOk]
  have moduleOk : ModuleInstOk (world bytes) frame.module context := by
    exact ModuleInstOk.mk (k := 0) (by simp [frame]) .nil .nil .nil
      (.cons (.mem (mi := memory bytes) rfl) .nil) .nil (by simp [frame]) .nil
      (by simp [frame]) (by simp [frame]) (by simp [frame]) (by simp [frame])
  exact ⟨context, ⟨storeOk, context, [], moduleOk, .nil, rfl⟩, instructions⟩

private theorem result_types_ok (count : Nat) : ResultOk context.toTypeCtx (resultTypes count) := by
  intro inst member
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp member
  exact .num _

private theorem seq_typed {bytes : ByteArray} {first second : List Admin} {params middle results : List CValType}
    (left : AdminsOk (world bytes) context first (.plain params middle))
    (right : AdminsOk (world bytes) context second (.plain middle results)) :
    AdminsOk (world bytes) context (first ++ second) (.plain params results) :=
  .seq left (by simp) right

private theorem framed {bytes : ByteArray} {params results : List CValType} {inst : Admin}
    (base : AdminOk (world bytes) context inst (.plain params results)) (count : Nat) :
    AdminsOk (world bytes) context [inst] (.plain (resultTypes count ++ params) (resultTypes count ++ results)) :=
  .frame (.single base) (result_types_ok count)

private theorem const_typed (bytes : ByteArray) (bits : BitVec 32) :
    AdminOk (world bytes) context (word bits).toAdmin (.plain [] [Ty.i32]) :=
  .plain (.numeric (.intConst .i32 bits))

private theorem code_typed (bytes : ByteArray) (code : Code input output) :
    AdminsOk (world bytes) context code.erase (.plain (resultTypes input) (resultTypes output)) := by
  induction code with
  | done => exact .id (result_types_ok _)
  | @const count output bits tail ih =>
    refine seq_typed (first := [(word bits).toAdmin]) ?_ ih
    simpa [resultTypes, List.replicate_succ'] using
      framed (const_typed bytes bits) count
  | @add count output tail ih =>
    refine seq_typed (first := [add]) ?_ ih
    have h : AdminOk (world bytes) context add (.plain [Ty.i32, Ty.i32] [Ty.i32]) :=
      .plain (.numeric (.intBinOp .i32 .add))
    simpa [resultTypes, List.replicate_succ', List.append_assoc] using
      framed h count
  | @load count output tail ih =>
    refine seq_typed (first := [load]) ?_ ih
    have h : AdminOk (world bytes) context load (.plain [Ty.i32] [Ty.i32]) :=
      .plain (.memory (.intLoad (a := .i32) rfl (memarg0_ok .i32 (by decide))))
    simpa [resultTypes, List.replicate_succ'] using framed h count
  | @store count output tail ih =>
    refine seq_typed (first := [store]) ?_ ih
    have h : AdminOk (world bytes) context store (.plain [Ty.i32, Ty.i32] []) :=
      .plain (.memory (.intStore (a := .i32) rfl (memarg0_ok .i32 (by decide))))
    simpa [resultTypes, List.replicate_succ', List.append_assoc] using framed h count

private theorem stack_typed (bytes : ByteArray) (stack : Stack input) :
    AdminsOk (world bytes) context (vals stack.values) (.plain [] (resultTypes input)) := by
  induction stack with
  | nil => exact .nil
  | @push count bits stack ih =>
    have next : AdminsOk (world bytes) context [(word bits).toAdmin]
        (.plain (resultTypes count) (resultTypes (count + 1))) := by
      simpa [resultTypes, List.replicate_succ'] using
        framed (const_typed bytes bits) count
    simpa [Stack.values, vals] using seq_typed ih next

theorem start_typed (code : Code input output) (stack : Stack input) {bytes : ByteArray}
    (page : bytes.size = Memory.pageSize) : ConfigOk (code.start stack bytes) (resultTypes output) :=
  config_typed page (seq_typed (stack_typed bytes stack) (code_typed bytes code))
end Silmaril.Proofs.Wasm.Execution.Core.MemoryProfile
