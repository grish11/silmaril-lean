module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Value)
open Computed

private theorem lookup_mem {program : Program} {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) : some fn ∈ program.functions := by
  cases slot : program.functions[address.value]? with
  | none => simp [Program.lookup, slot] at found
  | some data =>
    have same : data = some fn := by simpa [Program.lookup, slot] using found
    exact same ▸ List.mem_of_getElem? slot

theorem check_function {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.check = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 (some fn) (lookup_mem found)

theorem checked_v1_function {program : Program} (checked : program.checkV1 = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 ∧ codeV1 fn.code = true := by
  have guard := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 (some fn) (lookup_mem found)
  simpa only [Option.map_some, Option.getD_some, Bool.and_eq_true_iff, decide_eq_true_eq] using guard

theorem scalar_result {program : Program} (checked : program.checkV1 = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 :=
  (checked_v1_function checked found).1

theorem linked_target {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address := by
  have member : some fn.entry ∈ program.table.entries :=
    List.mem_map_of_mem (f := Option.map Function.entry) (lookup_mem found)
  obtain ⟨callee, lookup, resolves, declared, _⟩ :=
    (Table.check_iff program.table).mp (Program.rankCheck checked) fn.entry member target used
  rw [lookup_table] at lookup
  cases h : program.lookup target.address with
  | none => simp [h] at lookup
  | some body =>
    have same : body.entry = callee := by simpa [h] using lookup
    exact ⟨body, rfl, (congrArg Entry.declaration same).trans declared, resolves⟩

private theorem direct_function {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    program.checkLinkedFunction fn = true :=
  List.all_eq_true.mp checked (some fn) (lookup_mem found)

theorem check_direct_function {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) : fn.check = true :=
  (Bool.and_eq_true_iff.mp (direct_function checked found)).1

theorem linked_direct_target {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address := by
  have links := (Bool.and_eq_true_iff.mp (direct_function checked found)).2
  have valid := List.all_eq_true.mp links target used
  cases existsCallee : program.lookup target.address with
  | none => simp [existsCallee] at valid
  | some callee =>
    exact ⟨callee, rfl, by simpa [existsCallee] using valid⟩

theorem check_direct_of_ranked {program : Program} (checked : program.check = true) :
    program.checkDirect = true := by
  apply List.all_eq_true.mpr
  rintro (_ | fn) member
  · rfl
  · obtain ⟨index, bound, slot⟩ := List.mem_iff_getElem.mp member
    have found : program.lookup ⟨index⟩ = some fn := by
      simp [Program.lookup, List.getElem?_eq_getElem bound, slot]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨check_function checked found, List.all_eq_true.mpr ?_⟩
    intro target used
    obtain ⟨callee, lookup, declared, resolves⟩ := linked_target checked found used
    simp [lookup, declared, resolves]

theorem split_suffix {stack : List Value} {params : List NumType}
    (shape : SuffixTyped params stack) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = params := by
  unfold SuffixTyped at shape
  have length : min params.length stack.length = params.length := by
    simpa [Prefix.stackTypes] using congrArg List.length shape
  have enough : params.length ≤ stack.length := by omega
  let below := stack.length - params.length
  let saved := stack.take below
  let args := stack.drop below
  have stackEq : stack = saved ++ args := (List.take_append_drop below stack).symm
  have count : (Prefix.stackTypes args).length = params.length := by
    simp [Prefix.stackTypes, args, below]
    omega
  have split : Prefix.stackTypes stack = Prefix.stackTypes args ++ Prefix.stackTypes saved := by
    rw [stackEq]
    simp [Prefix.stackTypes]
  rw [split, ← count, List.take_left] at shape
  exact ⟨saved, args, stackEq, List.reverse_inj.mp shape⟩

private theorem stack_types_append (below above : List Value) :
    Prefix.stackTypes (below ++ above) = Prefix.stackTypes above ++ Prefix.stackTypes below := by
  simp [Prefix.stackTypes]

private theorem args_check {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {target : CallTarget} {saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length)
    (typed : fn.WellTyped (saved ++ operands) (.call target :: rest) fallthrough enclosing kind) :
    operands.map Value.type = target.declaration.params ∧ fn.ResumeTyped saved target rest fallthrough enclosing kind := by
  have length : operands.length = (Prefix.stackTypes operands).length := by simp [Prefix.stackTypes]
  unfold Function.WellTyped at typed
  simp only [checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq, stack_types_append, ← count, length,
    List.take_left, List.drop_left] at typed
  exact ⟨List.reverse_inj.mp typed.1.2, typed.2⟩

private theorem init_local_types {fn : Function} {args : List Value} (typed : args.map Value.type = fn.declaration.params) :
    (fn.declaration.frame args).locals.map Value.type = fn.localTypes := by
  simp [Declaration.frame, Function.localTypes, List.map_map, Function.comp_def, Value.zero, typed]

private theorem result_of_nil {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value} (typed : fn.WellTyped stack [] fallthrough enclosing kind) :
    stack.map Value.type = fallthrough := by
  simpa [Function.WellTyped, checkCode, Prefix.stackTypes] using typed

private theorem return_of_code {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value} {rest : List Op}
    (typed : fn.WellTyped stack (.return_ :: rest) fallthrough enclosing kind) : fn.ReturnTyped stack := by
  simpa [Function.WellTyped, Function.ReturnTyped, SuffixTyped, checkCode, checkOp] using typed

private theorem suffix_result {types : List NumType} {extra results : List Value}
    (typed : SuffixTyped types (extra ++ results)) (arity : results.length = types.length) :
    results.map Value.type = types := by
  have length : (Prefix.stackTypes results).length = types.length := by
    simpa [Prefix.stackTypes] using arity
  unfold SuffixTyped at typed
  rw [stack_types_append, ← length, List.take_left] at typed
  exact List.reverse_inj.mp typed

private theorem numeric_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {locals stack next : List Value} {op : Prefix.Op} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (step : Prefix.Reduce locals stack op (.values next))
    (body : fn.WellTyped stack (.numeric op :: rest) fallthrough enclosing kind) : fn.WellTyped next rest fallthrough enclosing kind := by
  have head := Prefix.checkOp_result step
  rw [typed] at head
  simpa [Function.WellTyped, checkCode, checkOp, head] using body

private theorem set_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {locals next saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (write : Locals.Edge ⟨locals, [.value v, .set i]⟩ ⟨next, []⟩)
    (body : fn.WellTyped (saved ++ [v]) (.set i :: rest) fallthrough enclosing kind) :
    next.map Value.type = fn.localTypes ∧ fn.WellTyped saved rest fallthrough enclosing kind := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type
  · have localGuard : Locals.Admitted fn.localTypes [] ⟨locals, [.value v, .set i]⟩ :=
      ⟨typed, by simp [Locals.check, fits]⟩
    exact ⟨(Locals.closed localGuard write).1,
      by simpa [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check, fits] using body⟩
  · simp [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check, fits] at body

private theorem tee_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (body : fn.WellTyped (saved ++ [v]) (.tee i :: rest) fallthrough enclosing kind) :
    fn.WellTyped (saved ++ [v, v]) (.set i :: rest) fallthrough enclosing kind := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type <;>
    simp_all [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check]

private theorem suffix_prefix {types : List NumType} {stack saved : List Value}
    (typed : SuffixTyped types stack) : SuffixTyped types (saved ++ stack) := by
  have enough : types.length ≤ (Prefix.stackTypes stack).length := by
    have count := congrArg List.length typed
    simp only [List.length_take, List.length_reverse] at count
    omega
  simpa only [SuffixTyped, stack_types_append, List.take_append_of_le_length enough] using typed

private theorem branching_guard {program : Program} {fn : Function} {fallthrough : List NumType}
    {enclosing : EnclosingLabels} {kind : LabelKind} {locals stack : List Value} {depth : LabelIdx} {result : List NumType}
    (ready : AdmittedAt program fn fallthrough enclosing (.branching locals stack depth result) kind) :
    locals.map Value.type = fn.localTypes ∧ enclosing[depth.toNat]? = some result ∧
      SuffixTyped result stack := by
  cases ready with | branching typed target payload => exact ⟨typed, target, payload⟩

private theorem returning_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    {locals stack : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.returning locals stack) kind) :
    locals.map Value.type = fn.localTypes ∧ fn.ReturnTyped stack := by
  cases ready with | returning locals stack => exact ⟨locals, stack⟩

private theorem exit_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    {locals stack : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.exit locals (.values stack)) kind) :
    locals.map Value.type = fn.localTypes ∧ stack.map Value.type = fallthrough := by
  cases ready with | exit locals stack => exact ⟨locals, stack⟩

private theorem restart_guard {program : Program} {fn : Function} {fallthrough : List NumType}
    {enclosing : EnclosingLabels} {kind : LabelKind} {locals : List Value}
    {result : Option NumType} {original : List Op}
    (ready : AdmittedAt program fn fallthrough enclosing (.restart locals result original) kind) :
    kind = .loop result original ∧ locals.map Value.type = fn.localTypes := by
  cases ready with | restart typed => exact ⟨rfl, typed⟩

private theorem indexed_restart_guard {program : Program} {fn : Function} {fallthrough : List NumType}
    {enclosing : EnclosingLabels} {kind : LabelKind} {locals args : List Value}
    {index : TypeIdx} {signature : Wasm.V1.FuncType} {original : List Op}
    (ready : AdmittedAt program fn fallthrough enclosing (.indexedRestart locals args index signature original) kind) :
    kind = .indexedLoop index signature original ∧ locals.map Value.type = fn.localTypes ∧
      args.map Value.type = signature.params := by
  cases ready with | indexedRestart typed params => exact ⟨rfl, typed, params⟩

private theorem trap_exit_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    {locals : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.exit locals .trap) kind) :
    locals.map Value.type = fn.localTypes := by
  cases ready with | exit locals _ => exact locals

private theorem split_condition {stack : List Value} {resume : List NumType → Bool}
    (typed : checkCondition (Prefix.stackTypes stack) resume = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  cases stack using List.reverseRecOn with
  | nil => simp [Prefix.stackTypes, checkCondition] at typed
  | append_singleton saved v =>
    rcases v with ⟨type, bits⟩
    rw [stack_types_append] at typed
    change checkCondition (type :: Prefix.stackTypes saved) resume = true at typed
    cases type with
    | float kind => simp [checkCondition] at typed
    | int kind =>
      cases kind with
      | i32 => exact ⟨saved, bits, rfl⟩
      | i64 => simp [checkCondition] at typed

theorem split_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : Option NumType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.if_ result thenBody elseBody :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

theorem split_indexed_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.indexedIf index signature thenBody elseBody :: rest) fallthrough enclosing kind) :
    ∃ (operands : List Value) (condition : BitVec 32), stack = operands ++ [Value.int .i32 condition] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

theorem indexed_if_arms {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {operands : List Value} {condition : BitVec 32} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped (operands ++ [Value.int .i32 condition])
      (.indexedIf index signature thenBody elseBody :: rest) fallthrough enclosing kind) :
    fn.WellTyped operands (.indexedBlock index signature thenBody :: rest) fallthrough enclosing kind ∧
    fn.WellTyped operands (.indexedBlock index signature elseBody :: rest) fallthrough enclosing kind := by
  unfold Function.WellTyped at typed
  rw [stack_types_append] at typed
  change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes operands) _ _ _ = true at typed
  simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at typed
  obtain ⟨⟨⟨resolved, left⟩, right⟩, resume⟩ := typed
  simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff]
  exact ⟨⟨⟨resolved, left⟩, resume⟩, ⟨⟨resolved, right⟩, resume⟩⟩

theorem split_br_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : List NumType} {depth : LabelIdx} {rest : List Op}
    (typed : fn.WellTyped stack (.brIf depth result :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

theorem split_br_table {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value}
    {result : List NumType} {depths : List LabelIdx} {fallback : LabelIdx} {rest : List Op}
    (typed : fn.WellTyped stack (.brTable depths fallback result :: rest) fallthrough enclosing kind) :
    ∃ (saved : List Value) (selector : BitVec 32), stack = saved ++ [Value.int .i32 selector] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

private theorem check_selected_branch {labels : List (List NumType)} {stack : List NumType}
    {depths : List LabelIdx} {fallback : LabelIdx} {result : List NumType}
    (fallbackOK : checkBranch labels stack fallback result = true)
    (entriesOK : (depths.all fun depth => checkBranch labels stack depth result) = true)
    (index : Nat) :
    checkBranch labels stack (depths[index]?.getD fallback) result = true := by
  cases found : depths[index]? with
  | none => exact fallbackOK
  | some depth => exact List.all_eq_true.mp entriesOK depth (List.mem_of_getElem? found)

theorem checked_branch {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    {stack : List Value} {depth : LabelIdx} {result : List NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing kind) :
    (branchTargets fallthrough enclosing kind)[depth.toNat]? = some result ∧ SuffixTyped result stack := by
  simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using typed

theorem branch_here_result {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {result : List NumType}
    (found : (branchTargets fallthrough enclosing kind)[(⟨0⟩ : LabelIdx).toNat]? = some result) :
    kind.inputs fallthrough = result := by
  change some (kind.inputs fallthrough) = some result at found
  exact Option.some.inj found

theorem frame_admitted_step {program : Program} (checked : program.checkDirect = true) (size : Nat) :
    ∀ {address fn a b fallthrough enclosing kind}, sizeOf a = size →
      program.lookup address = some fn → AdmittedAt program fn fallthrough enclosing a kind →
      program.FrameEdgeAt address kind a b → AdmittedAt program fn fallthrough enclosing b kind := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro address fn a b fallthrough enclosing kind sizeEq found ready move
    obtain ⟨callee, lookup, step⟩ := unfold_frame_edge.mp move
    have same := Option.some.inj (lookup.symm.trans found)
    subst callee
    rw [sizeEq] at step
    clear move sizeEq
    induction step generalizing fallthrough enclosing with
    | resolve args => cases ready with | call typed => exact .invoke typed
    | enter args typed =>
      cases ready
      exact .running (init_local_types typed) (check_direct_function checked found)
    | numeric step =>
      cases ready with
      | running typed body =>
        cases step
        · exact .running typed (numeric_preserves typed (.get ‹_›) body)
        · exact .running typed (numeric_preserves typed (.bin ‹_›) body)
        · exact .trapped typed
    | localSet write =>
      cases ready with
      | running typed body =>
        obtain ⟨nextTyped, restTyped⟩ := set_preserves typed write body
        exact .running nextTyped restTyped
    | localTee _ =>
      cases ready with
      | running typed body => exact .running typed (tee_preserves body)
    | ifSelect locals saved condition result thenBody elseBody rest =>
      cases ready with
      | running typed body =>
        unfold Function.WellTyped at body
        rw [stack_types_append] at body
        change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes saved) _ _ _ = true at body
        simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at body
        apply AdmittedAt.running typed
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff]
        split
        · exact ⟨body.1.2, body.2⟩
        · exact ⟨body.1.1, body.2⟩
    | indexedIfSelect _ _ condition _ _ _ _ _ =>
      cases ready with
      | running typed body =>
        obtain ⟨left, right⟩ := indexed_if_arms body
        apply AdmittedAt.running typed
        by_cases zero : condition = 0
        · simpa only [ite_eq_left zero] using right
        · simpa only [ite_eq_right zero] using left
    | blockEnter locals saved result code rest =>
      cases ready with
      | running typed body =>
        have both := body
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff] at both
        exact .block (.running typed both.1) both.2
    | @blockStep kind locals saved result rest inner next step bodyIH =>
      cases ready with
      | block inside resume =>
        have outcome := label_outcome step ⟨_, _, rfl⟩
        have after := bodyIH inside
        cases next with
        | label => exact .block after resume
        | branching =>
          obtain ⟨typed, target, payload⟩ := branching_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using
              And.intro target (suffix_prefix (saved := saved) payload))
        | returning =>
          obtain ⟨typed, out⟩ := returning_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Function.ReturnTyped, SuffixTyped, decide_eq_true_eq] using
              suffix_prefix (saved := saved) out)
        | exit locals out =>
          cases out with
          | values stack =>
            obtain ⟨typed, outTyped⟩ := exit_guard after
            exact .running typed (by simpa [Function.WellTyped, stack_types_append,
              Prefix.stackTypes, outTyped] using resume)
          | trap => exact .trapped (trap_exit_guard after)
        | restart => cases (restart_guard after).1
        | indexedRestart => cases (indexed_restart_guard after).1
        | call | invoke | done => cases outcome
    | indexedBlockEnter locals saved args index signature code rest resolved argsTyped =>
      cases ready with
      | running typed body =>
        have size : signature.params.length = (Prefix.stackTypes args).length := by
          simp [Prefix.stackTypes, argsTyped]
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff,
          stack_types_append, size, List.drop_left] at body
        exact .indexedBlock (.running typed (by simpa [Function.WellTyped, Prefix.stackTypes, argsTyped] using body.1.2)) body.2
    | @indexedBlockStep kind locals inner next saved signature rest step bodyIH =>
      cases ready with
      | indexedBlock inside resume =>
        have outcome := label_outcome step ⟨_, _, rfl⟩
        have after := bodyIH inside
        cases next with
        | label => exact .indexedBlock after resume
        | branching =>
          obtain ⟨typed, target, payload⟩ := branching_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using
              And.intro target (suffix_prefix (saved := saved) payload))
        | returning =>
          obtain ⟨typed, out⟩ := returning_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Function.ReturnTyped, SuffixTyped, decide_eq_true_eq] using
              suffix_prefix (saved := saved) out)
        | exit locals out =>
          cases out with
          | values stack =>
            obtain ⟨typed, outTyped⟩ := exit_guard after
            exact .running typed (by simpa [Function.WellTyped, stack_types_append,
              Prefix.stackTypes, outTyped] using resume)
          | trap => exact .trapped (trap_exit_guard after)
        | restart => cases (restart_guard after).1
        | indexedRestart => cases (indexed_restart_guard after).1
        | call | invoke | done => cases outcome
    | loopEnter locals saved result code rest =>
      cases ready with
      | running typed body =>
        have both := body
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff] at both
        exact .loop (.running typed both.1) both.1 both.2
    | @loopStep kind locals inner next saved result original rest step bodyIH =>
      cases ready with
      | loop inside originalTyped resume =>
        have outcome := label_outcome step ⟨_, _, rfl⟩
        have after := bodyIH inside
        cases next with
        | label => exact .loop after originalTyped resume
        | branching =>
          obtain ⟨typed, target, payload⟩ := branching_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using
              And.intro target (suffix_prefix (saved := saved) payload))
        | returning =>
          obtain ⟨typed, out⟩ := returning_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Function.ReturnTyped, SuffixTyped, decide_eq_true_eq] using
              suffix_prefix (saved := saved) out)
        | exit locals out =>
          cases out with
          | values stack =>
            obtain ⟨typed, outTyped⟩ := exit_guard after
            exact .running typed (by simpa [Function.WellTyped, stack_types_append,
              Prefix.stackTypes, outTyped] using resume)
          | trap => exact .trapped (trap_exit_guard after)
        | restart updated restarted body =>
          obtain ⟨same, typed⟩ := restart_guard after
          obtain ⟨rfl, rfl⟩ := LabelKind.loop.inj same
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff] using
              And.intro originalTyped resume)
        | call | invoke | done => cases outcome
        | indexedRestart => cases (indexed_restart_guard after).1
    | indexedLoopEnter locals saved args index signature code rest resolved argsTyped =>
      cases ready with
      | running typed body =>
        have size : signature.params.length = (Prefix.stackTypes args).length := by
          simp [Prefix.stackTypes, argsTyped]
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff,
          stack_types_append, size, List.drop_left] at body
        exact .indexedLoop
          (.running typed (by simpa [Function.WellTyped, Prefix.stackTypes, argsTyped] using body.1.2))
          resolved body.1.2 body.2
    | @indexedLoopStep kind locals inner next saved index signature original rest step bodyIH =>
      cases ready with
      | indexedLoop inside resolved originalTyped resume =>
        have outcome := label_outcome step ⟨_, _, rfl⟩
        have after := bodyIH inside
        cases next with
        | label => exact .indexedLoop after resolved originalTyped resume
        | branching =>
          obtain ⟨typed, target, payload⟩ := branching_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using
              And.intro target (suffix_prefix (saved := saved) payload))
        | returning =>
          obtain ⟨typed, out⟩ := returning_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Function.ReturnTyped, SuffixTyped, decide_eq_true_eq] using
              suffix_prefix (saved := saved) out)
        | exit locals out =>
          cases out with
          | values stack =>
            obtain ⟨typed, outTyped⟩ := exit_guard after
            exact .running typed (by simpa [Function.WellTyped, stack_types_append,
              Prefix.stackTypes, outTyped] using resume)
          | trap => exact .trapped (trap_exit_guard after)
        | restart => cases (restart_guard after).1
        | indexedRestart updated args restarted signature' body =>
          obtain ⟨same, typed, argsTyped⟩ := indexed_restart_guard after
          obtain ⟨rfl, rfl, rfl⟩ := LabelKind.indexedLoop.inj same
          have shape : Prefix.stackTypes args = signature.params.reverse := by simp [Prefix.stackTypes, argsTyped]
          have size : signature.params.length = (Prefix.stackTypes args).length := by simp [Prefix.stackTypes, argsTyped]
          apply AdmittedAt.running typed
          simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq,
            stack_types_append, size, List.take_left, List.drop_left]
          exact ⟨⟨⟨resolved, shape⟩, originalTyped⟩, resume⟩
        | call | invoke | done => cases outcome
    | unreachable args stack rest => cases ready with | running typed _ => exact .trapped typed
    | dispatch args saved operands target rest used count =>
      cases ready with
      | running typed body =>
        obtain ⟨callee, calleeFound, declared, _⟩ := linked_direct_target checked found used
        obtain ⟨callArgs, resume⟩ := args_check count body
        exact .active typed used calleeFound declared trivial (.invoke (callArgs.trans (congrArg Declaration.params declared).symm)) resume
    | child args saved target rest used live step =>
      cases ready with
      | active typed _ childFound declared _ childReady resume =>
        obtain ⟨smaller, childStep⟩ := step
        have next := ih _ smaller rfl childFound childReady childStep
        cases next with
        | call newArgs =>
          exact (frame_not_call childStep _ rfl).elim
        | invoke newArgs => exact .active typed used childFound declared trivial (.invoke newArgs) resume
        | running newArgs body => exact .active typed used childFound declared trivial (.running newArgs body) resume
        | active newArgs edge alloc same live ready body =>
          exact .active typed used childFound declared trivial (.active newArgs edge alloc same live ready body) resume
        | block inside body => exact .active typed used childFound declared trivial (.block inside body) resume
        | indexedBlock inside body => exact .active typed used childFound declared trivial (.indexedBlock inside body) resume
        | loop inside original body =>
          exact .active typed used childFound declared trivial (.loop inside original body) resume
        | indexedLoop inside resolved original body =>
          exact .active typed used childFound declared trivial (.indexedLoop inside resolved original body) resume
        | trapped newArgs => exact .active typed used childFound declared trivial (.trapped newArgs) resume
        | branching _ target _ => simp at target
        | returning newArgs out => exact .active typed used childFound declared trivial (.returning newArgs out) resume
        | exit newArgs out => exact .active typed used childFound declared trivial (.exit newArgs out) resume
        | @done _ _ _ _ result out =>
          cases result with
          | trap => exact .trapped typed
          | values stack =>
            have values : stack.map Value.type = target.declaration.results :=
              out.trans (congrArg Declaration.results declared)
            exact .running typed (by simpa [Function.WellTyped, Function.ResumeTyped, stack_types_append,
              Prefix.stackTypes, values] using resume)
    | discard cut => cases ready with | trapped typed => exact .trapped typed
    | branchIf locals stack condition depth result rest =>
      cases ready with
      | running typed body =>
        unfold Function.WellTyped at body
        rw [stack_types_append] at body
        change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes stack) _ _ _ = true at body
        simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at body
        apply AdmittedAt.running typed
        split
        · exact body.2
        · exact body.1
    | branchTable locals stack selector depths fallback result rest =>
      cases ready with
      | running typed body =>
        unfold Function.WellTyped at body
        rw [stack_types_append] at body
        change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes stack) _ _ _ = true at body
        simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at body
        exact .running typed (check_selected_branch body.1 body.2 selector.toNat)
    | @branchHere kind locals extra values result rest arity =>
      cases ready with
      | running typed body =>
        obtain ⟨target, payload⟩ := checked_branch body
        cases kind with
        | exit | indexed => exact .exit typed ((suffix_result payload arity).trans (branch_here_result target).symm)
        | loop result original => exact .restart typed
        | indexedLoop index signature original =>
          exact .indexedRestart typed ((suffix_result payload arity).trans (branch_here_result target).symm)
    | branchOuter locals stack depth result rest outer =>
      cases ready with
      | running typed body =>
        obtain ⟨target, payload⟩ := checked_branch body
        obtain ⟨index, eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt outer)
        refine .branching typed ?_ payload
        change enclosing[depth.toNat - 1]? = some result
        simpa [branchTargets, eq] using target
    | returnLabel _ _ _ =>
      cases ready with | running typed body => exact .returning typed (return_of_code body)
    | returnFrame _ _ _ arity =>
      cases ready with | returning _ out => exact .done (suffix_result out arity)
    | leaveValues args stack =>
      cases ready with | running typed body => exact .exit typed (result_of_nil body)
    | leaveTrap args => cases ready with | trapped typed => exact .exit typed trivial
    | leaveFrame args result typed => exact .done typed

theorem admitted_step {program : Program} (checked : program.check = true) (address : FuncAddr)
    {fn a b fallthrough enclosing kind} (found : program.lookup address = some fn)
    (ready : AdmittedAt program fn fallthrough enclosing a kind) (move : program.EdgeAt checked address kind a b) :
    AdmittedAt program fn fallthrough enclosing b kind :=
  frame_admitted_step (check_direct_of_ranked checked) _ rfl found ready
    ((frame_edge_iff_ranked checked address).mpr move)

theorem nesting_of_admitted {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {phase : Phase} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind}
    (found : program.lookup address = some fn)
    (ready : AdmittedAt program fn fallthrough enclosing phase kind) : program.table.Nesting (phase.frames address) := by
  induction ready generalizing address with
  | @active fn _ _ _ args saved target q rest callee typed used calleeFound declared live ready resume ih =>
    have resolved := target_resolved checked found used
    have nested := ih calleeFound
    cases q with
    | call | branching | restart | indexedRestart => cases live
    | invoke => simp [Phase.frames, Body.frames]
    | label => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | returning | exit => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | done => cases live
  | block _ _ ih | indexedBlock _ _ ih | loop _ _ _ ih | indexedLoop _ _ _ _ ih => exact ih found
  | _ => simp [Phase.frames, Body.frames]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
