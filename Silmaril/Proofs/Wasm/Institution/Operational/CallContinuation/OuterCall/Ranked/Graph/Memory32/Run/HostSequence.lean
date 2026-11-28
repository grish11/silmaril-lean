module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostEntry
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostControl
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs

open Execution.Runtime (AdminInstr EvalCtx Frame MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution
open ControlProofs
open HostEntry.Proofs (invoke_exact literal_expression numeric_expression framed_numeric_step framed_direct_step
  framed_trapped_step bytes_unique)

private theorem encode_expression {H : Type} (seq : Sequence H) (rest : List (HostSegment H)) (nextSource : Option (Source H)) :
    expression (encode Graph.v1CodeSyntax.ops (seq.endCode nextSource) rest) = seq.continuation rest nextSource := by
  induction rest with
  | nil => rfl
  | cons segment rest ih =>
    change expression (segment.operands.map (Prefix.emit Graph.v1CodeSyntax.ops) ++
      .call segment.site.index :: encode Graph.v1CodeSyntax.ops (seq.endCode nextSource) rest) = _
    rw [expression_append, numeric_expression]
    exact congrArg (fun tail => segment.operands.map (Prefix.emit v1Syntax) ++ .source (.call segment.site.index) :: tail) ih

section Execution

variable {H : Type} {seq : Sequence H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {start : ByteArray} {outer : Frame} {args : List Value} {source : Source H}

local notation "live" => storeWithBytes base memory initial
local notation "renderPhase" => seq.render base memory initial start outer args
local notation "active" => seq.root.function.declaration.frame args
local notation "arity" => seq.root.function.declaration.results.length
local notation "rootFn" => seq.root.function
local notation "contextAt" => seq.context args

private theorem render_hosts (bytes : ByteArray) (stack : List Value) (labels : List (OpenLabel H))
    (first : HostSegment H) (later : List (HostSegment H)) (nextSource : Option (Source H)) :
    renderPhase (.computing bytes stack first.operands first.site later labels nextSource) =
      ⟨live bytes, outer, (contextAt labels).plug value
        (values stack ++ expression (encode Graph.v1CodeSyntax.ops (seq.endCode nextSource) (first :: later)))⟩ := by
  rw [encode_expression]
  simp only [continuation, encode, v1Syntax, Function.comp_apply, render, List.append_assoc]

private theorem render_finish (bytes : ByteArray) (stack : List Value) (code : List Op)
    (labels : List (OpenLabel H)) :
    renderPhase (seq.finish outer args bytes stack code labels) =
      ⟨live bytes, outer, (contextAt labels).plug value (values stack ++ expression (v1Code code))⟩ := by
  cases labels with
  | nil => rfl
  | cons label rest =>
    simp only [finish]
    split
    · rename_i completes
      have empty : code = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp completes).2
      subst code
      simp [render, v1Code, expression]
    · rfl

private theorem render_begin (bytes : ByteArray) (stack : List Value) (labels : List (OpenLabel H)) (region : Source H) :
    renderPhase (seq.beginBody outer args bytes stack labels region) =
      ⟨live bytes, outer, (contextAt labels).plug value (values stack ++ expression (seq.sourceCode region))⟩ := by
  cases region with
  | root => exact render_hosts bytes stack labels seq.first seq.later none
  | hostSequence first later => exact render_hosts bytes stack labels first later none
  | hostsThen first later tail => exact render_hosts bytes stack labels first later (some tail)
  | br | brIf | brTable => rfl
  | plain code => exact render_finish bytes stack code labels
  | blockThen | ifThen | loopThen => rfl

private theorem enter_step {dst : Config H} (checked : seq.Checked mode program memory calls base outer args source) :
    Step host (renderPhase (.invoke source)) dst ↔
      dst = renderPhase (seq.beginBody outer args start (rootFn).initial [] source) := by
  have count : args.length = (rootFn).declaration.params.length := by simpa using congrArg List.length checked.parameters
  have allocated : (live start).funcs[seq.root.address.value]? =
      some (.wasm (rootFn).declaration.type (rootFn).declaration.module (seq.v1FuncFor source)) := checked.allocated
  have body : expression (seq.v1FuncFor source).body =
      values (rootFn).initial ++ expression (seq.sourceCode source) := by
    change expression ((rootFn).initial.map Graph.v1CodeSyntax.ops.value ++ seq.sourceCode source) = _
    rw [expression_append, literal_expression]
  have locals : (seq.v1FuncFor source).locals = (rootFn).declaration.locals := rfl
  rw [render_begin]
  simpa only [render, body, locals, context, labelCode,
    OpenLabel.labelArity, insert, EvalCtx.comp, EvalCtx.plug, Declaration.frame] using
    (invoke_exact (host := host) (outer := outer) (dst := dst) allocated count checked.scalar)

private theorem root_call {current : Source H} {dst : Config H}
    (checked : seq.Checked mode program memory calls base outer args source) :
    Step host (renderPhase (.call current)) dst ↔ dst = renderPhase (.invoke current) :=
  HostCall.V1.direct_step_iff (tail := []) checked.resolved

private theorem block_entry {bytes : ByteArray} {stack : List Value} {result : Option NumType}
    {region tail : Source H} {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.block bytes stack result region tail labels)) dst ↔
      dst = renderPhase (seq.beginBody outer args bytes [] (.block stack result tail :: labels) region) := by
  rw [render_begin, open_code]
  exact scoped_block_iff seq args labels

private theorem loop_entry {bytes : ByteArray} {stack : List Value} {region tail : Source H} {result : Option NumType}
    {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.loop bytes stack region tail labels result)) dst ↔
      dst = renderPhase (seq.beginBody outer args bytes [] (.loop stack region tail result :: labels) region) := by
  rw [render_begin, open_code]
  exact scoped_loop_iff seq args labels

private theorem condition_step {bytes : ByteArray} {stack : List Value} {result : Option NumType} {index : LocalIdx}
    {left right tail : Source H} {condition : BitVec 32} {labels : List (OpenLabel H)} {dst : Config H}
    (found : (active).locals[index.toNat]? = some (.int .i32 condition)) :
    Step host (renderPhase (.if_ bytes stack result index left right tail labels)) dst ↔
      dst = renderPhase (.test bytes stack result index left right tail condition labels) :=
  scoped_get_iff seq args labels found

private theorem select_step {bytes : ByteArray} {stack : List Value} {result : Option NumType} {index : LocalIdx}
    {left right tail : Source H} {condition : BitVec 32} {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.test bytes stack result index left right tail condition labels)) dst ↔
      dst = renderPhase (.block bytes stack result (if condition = 0 then right else left) tail labels) := by
  have rule := scoped_if_iff (H := H) (host := host) (s := live bytes) (outer := outer) seq args labels
    (stack := stack) (condition := condition) (result := result) (left := seq.sourceCode left)
    (right := seq.sourceCode right) (tail := expression (seq.sourceCode tail)) (dst := dst)
  by_cases zero : condition = 0
  · rw [ite_eq_left zero] at rule ⊢
    exact rule
  · rw [ite_eq_right zero] at rule ⊢
    exact rule

private theorem close_label_step {bytes : ByteArray} {stack : List Value} {label : OpenLabel H}
    {rest : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.completed bytes stack label rest)) dst ↔
      dst = renderPhase (seq.beginBody outer args bytes (label.saved ++ stack) rest label.tail) := by
  let n := (OpenLabel.labelArity (rootFn) (label :: rest))
  have atLabel (target : Config H) :
      Step host ⟨live bytes, outer, [.frame n active [.label n (seq.labelCode (label :: rest)) (values stack)]]⟩ target ↔
        ∃ outcome : Unit, True ∧ target = ⟨live bytes, outer, [.frame n active (values stack)]⟩ := by
    rw [HostEntry.Proofs.frame_label_step]
    constructor
    · rintro (⟨_, _, _, move, _⟩ | ⟨out, pure, eq⟩)
      · exact (move.firstRedex_ne_none (firstRedex_values stack)).elim
      · have same := HostEntry.Proofs.label_values pure rfl
        exact ⟨(), trivial, same ▸ eq⟩
    · rintro ⟨_, _, rfl⟩
      exact .inr ⟨_, .labelDone n (seq.labelCode (label :: rest)) stack, rfl⟩
  rw [render_begin]
  simp only [render]
  rw [scoped_result seq args (label :: rest) (fun _ : Unit => True) (fun _ => values stack) atLabel]
  simp [context_code, insert, EvalCtx.plug_comp, EvalCtx.plug, tailCode, values, List.append_assoc]

theorem loop_fallthrough_step {bytes : ByteArray} {saved stack : List Value} {result : Option NumType}
    {region tail : Source H} {labels : List (OpenLabel H)} {dst : Config H}
    (ready : seq.Ready mode program memory calls initial (.completed bytes stack (.loop saved region tail result) labels) source) :
    Step host (renderPhase (.completed bytes stack (.loop saved region tail result) labels)) dst ↔
      stack.map Value.type = result.toList ∧
        dst = renderPhase (seq.beginBody outer args bytes (saved ++ stack) labels tail) := by
  rw [close_label_step]
  exact ⟨fun eq => ⟨ready.2.1, eq⟩, And.right⟩

private theorem branch_test_step {bytes : ByteArray} {saved : List Value} {branch : ForwardBranch}
    {tail : Source H} {condition : BitVec 32} {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.branchTest bytes (saved ++ [Value.int .i32 condition]) branch tail labels)) dst ↔
      dst = renderPhase (if condition = 0 then seq.beginBody outer args bytes saved labels tail
        else .branching bytes saved branch (expression (seq.sourceCode tail)) labels) := by
  have selected := scoped_br_if_iff (host := host) (s := live bytes) (outer := outer) seq args labels
    (saved := saved) (condition := condition) (depth := branch.depth) (tail := expression (seq.sourceCode tail)) (dst := dst)
  by_cases zero : condition = 0
  · rw [ite_eq_left zero] at selected ⊢
    rw [render_begin]
    simpa only [render, List.append_assoc, List.nil_append] using selected
  · rw [ite_eq_right zero] at selected ⊢
    simpa only [render, List.append_assoc, List.singleton_append] using selected

private theorem table_select_step {bytes : ByteArray} {saved : List Value} {table : ForwardTable}
    {selector : BitVec 32} {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.tableSelect bytes (saved ++ [Value.int .i32 selector]) table labels)) dst ↔
      dst = renderPhase (.branching bytes saved (table.select selector) [] labels) :=
  scoped_br_table_iff seq args labels

private theorem branch_step {bytes : ByteArray} {stack : List Value} {branch : ForwardBranch}
    {skipped : List Admin} {label : OpenLabel H} {rest : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.branching bytes stack branch skipped (label :: rest))) dst ↔
      (∃ extra payload, stack = extra ++ payload ∧ payload.length = label.branchTypes.length ∧
        branch.depth.toNat = 0 ∧ dst = renderPhase (seq.branchDestination outer args bytes payload label rest)) ∨
      (0 < branch.depth.toNat ∧ dst = renderPhase (.branching bytes (label.saved ++ stack)
        { branch with depth := lowerLabel branch.depth } (seq.tailCode label) rest)) := by
  let n := label.branchTypes.length
  let moves : Option (List Value × List Value) → Prop
    | none => 0 < branch.depth.toNat
    | some (extra, payload) => stack = extra ++ payload ∧ payload.length = n ∧ branch.depth.toNat = 0
  let output : Option (List Value × List Value) → List Admin
    | none => values stack ++ [.source (.br (lowerLabel branch.depth))]
    | some (_, payload) => values payload ++ expression (seq.labelCode (label :: rest))
  have atLabel (target : Config H) :
      Step host ⟨live bytes, outer, [.frame n active
        [.label n (seq.labelCode (label :: rest)) (values stack ++ .source (.br branch.depth) :: skipped)]]⟩ target ↔
      ∃ answer, moves answer ∧ target = ⟨live bytes, outer, [.frame n active (output answer)]⟩ := by
    rw [framed_branch_iff]
    constructor
    · rintro (⟨extra, payload, split, count, zero, eq⟩ | ⟨positive, eq⟩)
      · exact ⟨some (extra, payload), ⟨split, count, zero⟩, eq⟩
      · exact ⟨none, positive, eq⟩
    · rintro ⟨out | ⟨extra, payload⟩, moved, eq⟩
      · exact .inr ⟨moved, eq⟩
      · exact .inl ⟨extra, payload, moved.1, moved.2.1, moved.2.2, eq⟩
  change Step host ⟨live bytes, outer, (contextAt (label :: rest)).plug value
    (values stack ++ .source (.br branch.depth) :: skipped)⟩ dst ↔ _
  rw [scoped_result seq args (label :: rest) moves output atLabel]
  have after (code : List Admin) :
      seq.afterLabel args (label :: rest) code =
        (contextAt rest).plug value (values label.saved ++ code ++ seq.tailCode label) := by
    simp [afterLabel, insert, EvalCtx.plug_comp, EvalCtx.plug, context_code, values, List.append_assoc]
  have exits (payload : List Value) (count : payload.length = label.branchTypes.length) :
      renderPhase (seq.branchDestination outer args bytes payload label rest) =
        ⟨live bytes, outer, seq.afterLabel args (label :: rest) (output (some ([], payload)))⟩ := by
    rw [after]
    cases label with
    | block saved result tail =>
      rw [branchDestination, render_begin]
      simp [output, labelCode, tailCode, OpenLabel.tail, OpenLabel.saved, values_append, List.append_assoc, expression]
    | loop saved region tail result =>
      have empty : payload = [] := List.eq_nil_of_length_eq_zero count
      subst payload
      simp [branchDestination, render, sourceCode, output, labelCode, tailCode, OpenLabel.tail, OpenLabel.saved,
        expression, values, List.append_assoc]
  have lowers :
      renderPhase (.branching bytes (label.saved ++ stack) { branch with depth := lowerLabel branch.depth }
        (seq.tailCode label) rest) = ⟨live bytes, outer, seq.afterLabel args (label :: rest) (output none)⟩ := by
    rw [after]
    simp [render, output, values_append, List.append_assoc]
  constructor
  · rintro ⟨_ | ⟨extra, payload⟩, moved, eq⟩
    · exact .inr ⟨moved, eq.trans lowers.symm⟩
    · exact .inl ⟨extra, payload, moved.1, moved.2.1, moved.2.2, eq.trans (exits payload moved.2.1).symm⟩
  · rintro (⟨extra, payload, split, count, zero, eq⟩ | ⟨positive, eq⟩)
    · exact ⟨some (extra, payload), ⟨split, count, zero⟩, eq.trans (exits payload count)⟩
    · exact ⟨none, positive, eq.trans lowers⟩

theorem loop_restart_step {bytes : ByteArray} {stack saved : List Value} {results : List NumType}
    {result : Option NumType} {region tail : Source H} {skipped : List Admin} {rest : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.branching bytes stack ⟨⟨0⟩, results⟩ skipped (.loop saved region tail result :: rest))) dst ↔
      dst = renderPhase (.loop bytes saved region tail rest result) := by
  constructor
  · intro step
    rcases branch_step.mp step with ⟨_, _, _, _, _, eq⟩ | ⟨positive, _⟩
    · exact eq
    · exact (Nat.not_lt_zero _ positive).elim
  · intro eq
    exact branch_step.mpr (.inl ⟨stack, [], (List.append_nil stack).symm, rfl, rfl, eq⟩)

private theorem numeric_step {bytes : ByteArray} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {site : HostCall.V1.Site H} {later : List (HostSegment H)} {labels : List (OpenLabel H)} {nextSource : Option (Source H)} {dst : Config H} :
    Step host (renderPhase (.computing bytes stack (op :: rest) site later labels nextSource)) dst ↔
      (∃ next, Prefix.Reduce (active).locals stack op (.values next) ∧
        dst = renderPhase (.computing bytes next rest site later labels nextSource)) ∨
      (∃ saved, Prefix.Reduce (active).locals stack op (.trap saved) ∧
        dst = renderPhase (.trapped bytes saved (rest.map (Prefix.emit v1Syntax) ++
          .source (.call site.index) :: seq.continuation later nextSource) labels)) := by
  let tail := rest.map (Prefix.emit v1Syntax) ++ .source (.call site.index) :: seq.continuation later nextSource
  let output out := [AdminInstr.label (OpenLabel.labelArity (rootFn) labels) (seq.labelCode labels) (Prefix.outcomeCode values .trap tail out)]
  have atLabel :
      ∀ target : Config H, Step host ⟨live bytes, outer, [.frame (OpenLabel.labelArity (rootFn) labels) active
        [.label (OpenLabel.labelArity (rootFn) labels) (seq.labelCode labels) (values stack ++ Prefix.emit v1Syntax op :: tail)]]⟩ target ↔
        ∃ out, Prefix.Reduce (active).locals stack op out ∧ target = ⟨live bytes, outer,
          [.frame (OpenLabel.labelArity (rootFn) labels) active (output out)]⟩ := by
    intro target
    rw [framed_numeric_step]
    constructor
    · rintro (⟨next, move, eq⟩ | ⟨saved, move, eq⟩)
      · exact ⟨.values next, move, eq⟩
      · exact ⟨.trap saved, move, eq⟩
    · rintro ⟨out, move, eq⟩
      cases out with
      | values next => exact .inl ⟨next, move, eq⟩
      | trap saved => exact .inr ⟨saved, move, eq⟩
  simp only [render, List.map_cons, List.append_assoc, List.cons_append]
  change Step host ⟨live bytes, outer, (contextAt labels).plug value (values stack ++ Prefix.emit v1Syntax op :: tail)⟩ dst ↔ _
  rw [scoped_result seq args labels (fun out => Prefix.Reduce (active).locals stack op out) output atLabel]
  simp only [context_code]
  constructor
  · rintro ⟨out, move, eq⟩
    cases out with
    | values next => exact .inl ⟨next, move, eq⟩
    | trap saved => exact .inr ⟨saved, move, eq⟩
  · rintro (⟨next, move, eq⟩ | ⟨saved, move, eq⟩)
    · exact ⟨.values next, move, eq⟩
    · exact ⟨.trap saved, move, eq⟩

private theorem host_call {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List (OpenLabel H)} {nextSource : Option (Source H)} {dst : Config H}
    (linked : Linked site (rootFn).declaration.module base) :
    Step host (renderPhase (.computing bytes (saved ++ actual) [] site later labels nextSource)) dst ↔
      dst = renderPhase (.pending bytes saved actual site later labels nextSource) := by
  simp only [render, List.map_nil, List.append_nil]
  exact scoped_source_iff seq args labels rfl (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => HostCall.V1.direct_step_iff (caller := active) linked.resolved)

private theorem render_close_trapped (bytes : ByteArray) (labels : List (OpenLabel H)) :
    renderPhase (seq.closeTrapped outer args bytes labels) = ⟨live bytes, outer, seq.afterLabel args labels [.trap]⟩ := by
  cases labels with
  | nil => rfl
  | cons label rest =>
    simp only [closeTrapped]
    split
    · simp [render, afterLabel, context_code, insert, EvalCtx.plug_comp, EvalCtx.plug, values, List.append_assoc]
    · rfl

private theorem trap_step {bytes : ByteArray} {saved : List Value} {tail : List Admin}
    {labels : List (OpenLabel H)} {dst : Config H} :
    Step host (renderPhase (.trapped bytes saved tail labels)) dst ↔
      (∃ kept rest, Prefix.Discard saved tail kept rest ∧ dst = renderPhase (.trapped bytes kept rest labels)) ∨
      (saved = [] ∧ tail = [] ∧ dst = renderPhase (seq.closeTrapped outer args bytes labels)) := by
  let outcome : Option (List Value × List Admin) → List Admin
    | none => [.trap]
    | some (kept, rest) => [.label (OpenLabel.labelArity (rootFn) labels) (seq.labelCode labels) (values kept ++ .trap :: rest)]
  let moves : Option (List Value × List Admin) → Prop
    | none => saved = [] ∧ tail = []
    | some (kept, rest) => Prefix.Discard saved tail kept rest
  have atLabel :
      ∀ target : Config H, Step host ⟨live bytes, outer, [.frame (OpenLabel.labelArity (rootFn) labels) active
        [.label (OpenLabel.labelArity (rootFn) labels) (seq.labelCode labels) (values saved ++ .trap :: tail)]]⟩ target ↔
        ∃ out, moves out ∧ target = ⟨live bytes, outer,
          [.frame (OpenLabel.labelArity (rootFn) labels) active (outcome out)]⟩ := by
    intro target
    rw [framed_trapped_step]
    constructor
    · rintro (⟨kept, rest, move, eq⟩ | ⟨empty, noTail, eq⟩)
      · exact ⟨some (kept, rest), move, eq⟩
      · exact ⟨none, ⟨empty, noTail⟩, eq⟩
    · rintro ⟨out, move, eq⟩
      rcases out with _ | ⟨kept, rest⟩
      · exact .inr ⟨move.1, move.2, eq⟩
      · exact .inl ⟨kept, rest, move, eq⟩
  rw [render_close_trapped]
  simp only [render, afterLabel]
  rw [scoped_result seq args labels moves outcome atLabel]
  simp only [context_code]
  constructor
  · rintro ⟨out, move, eq⟩
    rcases out with _ | ⟨kept, rest⟩
    · exact .inr ⟨move.1, move.2, eq⟩
    · exact .inl ⟨kept, rest, move, eq⟩
  · rintro (⟨kept, rest, move, eq⟩ | ⟨empty, noTail, eq⟩)
    · exact ⟨some (kept, rest), move, eq⟩
    · exact ⟨none, ⟨empty, noTail⟩, eq⟩

private theorem render_delivered {bytes : ByteArray} {saved : List Value} {later : List (HostSegment H)}
    {labels : List (OpenLabel H)} {nextSource : Option (Source H)} (r : Execution.Runtime.Result) :
    renderPhase (seq.delivered outer args bytes saved later r labels nextSource) =
      ⟨live bytes, outer, (contextAt labels).plug value (values saved ++ result r ++ seq.continuation later nextSource)⟩ := by
  cases r with
  | trap => simp [delivered, render, result, List.append_assoc]
  | values vs =>
    cases later with
    | nil =>
      cases nextSource with
      | none => simp [delivered, resume, render_finish, continuation, encode, result, endCode, List.append_assoc]
      | some => simp [delivered, resume, render_begin, continuation, encode, result, endCode, List.append_assoc]
    | cons => simp [delivered, resume, render, continuation, encode, v1Syntax, result, List.append_assoc]

private theorem pending_step {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List (OpenLabel H)} {nextSource : Option (Source H)} {dst : Config H}
    (linked : Linked site (rootFn).declaration.module base)
    (typed : actual.map Value.type = site.signature.params) :
    Step host (renderPhase (.pending bytes saved actual site later labels nextSource)) dst ↔
      (∃ s' r, host site.target (live bytes) actual (.returned s' r) ∧
        dst = ⟨s', outer, (contextAt labels).plug value (values saved ++ result r ++ seq.continuation later nextSource)⟩) ∨
      (host site.target (live bytes) actual .diverged ∧
        dst = renderPhase (.pending bytes saved actual site later labels nextSource)) := by
  have siteChecked : site.Checked (live bytes) ((contextAt labels).activeFrame outer) actual := by
    rw [active_frame]
    exact ⟨linked.resolved, linked.allocated, typed, linked.scalar⟩
  exact v1_host_pending_step_iff (k := contextAt labels) (outer := outer)
    (saved := saved) (tail := seq.continuation later nextSource) siteChecked

private theorem label_scalar (checked : seq.Checked mode program memory calls base outer args source)
    (labels : List (OpenLabel H)) : (OpenLabel.labelArity (rootFn) labels) ≤ 1 := by
  cases labels with
  | nil => exact checked.scalar
  | cons label rest =>
    cases label with
    | block _ result _ =>
      change result.toList.length ≤ 1
      cases result <;> simp
    | loop => exact Nat.zero_le _

private theorem plain_label_code {labels : List (OpenLabel H)} (plain : OpenLabel.needsResume labels = false) :
    seq.labelCode labels = [] := by
  cases labels with
  | nil => rfl
  | cons label rest =>
    cases label with
    | block => rfl
    | loop => simp [OpenLabel.needsResume] at plain

private theorem insert_allowed (checked : seq.Checked mode program memory calls base outer args source)
    {labels : List (OpenLabel H)} (scopes : seq.ContextReady mode program memory calls source labels)
    (plain : OpenLabel.needsResume labels = false)
    {code : List Admin} (body : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls (rootFn).rank (active).module ((seq.insert labels).plug value code) := by
  induction labels generalizing code with
  | nil => exact body
  | cons label rest ih =>
    cases label with
    | loop => simp [OpenLabel.needsResume] at plain
    | block saved result tail =>
      have ⟨plainTail, plainRest⟩ := Bool.or_eq_false_iff.mp plain
      have allowed : CodeAllowedFor mode program memory calls (rootFn).rank (active).module
          (seq.tailCode (.block saved result tail)) := by
        cases tail <;> simp [Source.needsResume] at plainTail
        exact scopes.2.1
      simp only [insert, EvalCtx.plug_comp, EvalCtx.plug, plain_label_code plainRest]
      exact ih scopes.2.2.2.1 plainRest (RunProofs.single_allowed.mpr
        (.label (label_scalar checked rest)
          (RunProofs.append_allowed.mpr ⟨RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed saved, body⟩,
            allowed⟩)))

private theorem frame_allowed (checked : seq.Checked mode program memory calls base outer args source)
    {code : List Admin}
    (guard : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls ((rootFn).rank + 1) outer.module
      [AdminInstr.frame arity active code] := by
  have rank : calls.permits ((rootFn).rank + 1) (rootFn).rank := by cases calls <;> simp [CallMode.permits]
  exact RunProofs.single_allowed.mpr (.enteredFrame checked.scalar rank guard)

private theorem wrap_checked (checked : seq.Checked mode program memory calls base outer args source)
    {labels : List (OpenLabel H)} (scopes : seq.ContextReady mode program memory calls source labels)
    (plain : OpenLabel.needsResume labels = false)
    {code : List Admin} (guard : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls ((rootFn).rank + 1) outer.module ((contextAt labels).plug value code) := by
  rw [context_code, plain_label_code plain]
  exact frame_allowed checked (insert_allowed checked scopes plain
    (RunProofs.single_allowed.mpr (.label (label_scalar checked labels) guard)))

private theorem finish_ready (checked : seq.Checked mode program memory calls base outer args source)
    {bytes : ByteArray} {stack : List Value} {code : List Op} {labels : List (OpenLabel H)}
    (extent : mode.extent initial.data.size bytes)
    (typed : checkTail (rootFn) (Prefix.stackTypes stack) (OpenLabel.results (rootFn) labels)
      (OpenLabel.targets (rootFn) labels) (OpenLabel.needsResume labels) code = true)
    (scopes : seq.ContextReady mode program memory calls source labels)
    (allowed : CodeAllowedFor mode program memory calls (rootFn).rank (active).module (expression (v1Code code))) :
    seq.Ready mode program memory calls initial (seq.finish outer args bytes stack code labels) source := by
  have graph (plain : OpenLabel.needsResume labels = false) :
      seq.Ready mode program memory calls initial
        (.graph ⟨bytes, outer, (contextAt labels).plug value (values stack ++ expression (v1Code code))⟩) source :=
    ⟨extent, wrap_checked checked scopes plain
      (RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed stack, allowed⟩)⟩
  cases labels with
  | nil => exact graph rfl
  | cons label rest =>
    cases h : OpenLabel.needsResume (label :: rest) with
    | false => simpa only [finish, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte] using graph h
    | true =>
      simp only [checkTail, h, ↓reduceIte, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
      have types : stack.map Value.type = label.result.toList := by
        simpa [OpenLabel.results, Prefix.stackTypes] using typed.2
      simpa only [finish, h, Bool.true_and, typed.1, ↓reduceIte] using
        (show seq.Ready mode program memory calls initial (.completed bytes stack label rest) source from
          ⟨extent, types, scopes⟩)

private theorem computing_ready {bytes : ByteArray} {stack : List Value} {first : HostSegment H}
    {later : List (HostSegment H)} {labels : List (OpenLabel H)} {nextSource : Option (Source H)}
    (extent : mode.extent initial.data.size bytes)
    (listed : ∀ site ∈ first.site :: later.map HostSegment.site, site ∈ seq.sourceSites source)
    (typed : seq.checkContinuation labels nextSource (Prefix.stackTypes stack) (first :: later) = true)
    (scopes : seq.ContextReady mode program memory calls source labels)
    (tailGuard : seq.ContinuationReady mode program memory calls source nextSource) :
    seq.Ready mode program memory calls initial (.computing bytes stack first.operands first.site later labels nextSource)
      source :=
  ⟨extent, listed _ (.head _), fun piece used => listed _ (.tail _ (List.mem_map.mpr ⟨piece, used, rfl⟩)),
    typed, scopes, tailGuard⟩

private theorem begin_ready {bytes : ByteArray} {region : Source H} {stack : List Value} {labels : List (OpenLabel H)}
    (checked : seq.Checked mode program memory calls base outer args source)
    (extent : mode.extent initial.data.size bytes)
    (ready : seq.SourceReady mode program memory calls labels stack region source) :
    seq.Ready mode program memory calls initial (seq.beginBody outer args bytes stack labels region) source := by
  cases region with
  | root =>
    obtain ⟨scopes, _, listed, typed⟩ := ready
    exact computing_ready (first := seq.first) (later := seq.later) extent listed typed scopes trivial
  | hostSequence first later =>
    obtain ⟨scopes, _, listed, typed⟩ := ready
    exact computing_ready (first := first) (later := later) extent listed typed scopes trivial
  | hostsThen first later tail =>
    obtain ⟨scopes, allowed, listed, typed⟩ := ready
    exact computing_ready extent (fun site used => listed site (List.mem_append_left _ used)) typed scopes
      ⟨allowed, fun site used => listed site (List.mem_append_right _ used)⟩
  | br branch => exact ⟨extent, ready.2.2.2, ready.1⟩
  | plain code => exact finish_ready checked extent ready.2.2.2 ready.1 ready.2.1
  | blockThen | ifThen | brIf | brTable | loopThen => exact ⟨extent, ready⟩

private theorem resume_ready (checked : seq.Checked mode program memory calls base outer args source)
    {bytes : ByteArray} {stack : List Value} {later : List (HostSegment H)} {labels : List (OpenLabel H)}
    {nextSource : Option (Source H)}
    (extent : mode.extent initial.data.size bytes) (listed : ∀ piece ∈ later, piece.site ∈ seq.sourceSites source)
    (typed : seq.checkContinuation labels nextSource (Prefix.stackTypes stack) later = true)
    (scopes : seq.ContextReady mode program memory calls source labels)
    (tailGuard : seq.ContinuationReady mode program memory calls source nextSource) :
    seq.Ready mode program memory calls initial (seq.resume outer args bytes stack later labels nextSource) source := by
  cases later with
  | nil =>
    cases nextSource with
    | none =>
      apply finish_ready checked extent typed scopes
      apply RunProofs.tail_allowed (fn := rootFn) ?_ checked.slot checked.supportedTail
      intro target used
      obtain ⟨callee, found, _, linked, permitted⟩ := checked.linkedTail target used
      exact ⟨callee, found, linked, permitted⟩
    | some region => exact begin_ready checked extent ⟨scopes, tailGuard.1, tailGuard.2, typed⟩
  | cons piece rest =>
    exact ⟨extent, listed piece (.head _), fun later used => listed later (.tail _ used), typed, scopes, tailGuard⟩

theorem return_ready (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (contract : seq.Contract host mode memory initial base source)
    {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List (OpenLabel H)} {nextSource : Option (Source H)} {after : Store H} {r : Execution.Runtime.Result}
    (ready : seq.Ready mode program memory calls initial (.pending bytes saved actual site later labels nextSource) source)
    (returned : host site.target (live bytes) actual (.returned after r)) :
    ∃ next, after = live next ∧ bytes.size ≤ next.size ∧ HostCall.V1.ResultTyped site.signature.results r ∧
      Layout program after memory { initial with data := next } ∧
      seq.Ready mode program memory calls initial (seq.delivered outer args next saved later r labels nextSource) source := by
  obtain ⟨extent, listed, laterListed, typedArgs, continuation, scopes⟩ := ready
  obtain ⟨typed, storeEffect⟩ := contract site listed bytes extent actual typedArgs after r returned
  obtain ⟨next, stored, newExtent, mono, allocation⟩ := layout.host_store extent storeEffect
  refine ⟨next, stored, mono, typed, allocation, ?_⟩
  cases r with
  | trap => exact ⟨newExtent, scopes.1⟩
  | values payload =>
    apply resume_ready checked newExtent laterListed _ scopes.1 scopes.2
    have payloadTyped : payload.map Value.type = site.signature.results := typed
    simpa [Prefix.stackTypes, payloadTyped] using continuation

private theorem locals_typed (checked : seq.Checked mode program memory calls base outer args source) :
    (active).locals.map Value.type = (rootFn).declaration.params ++ (rootFn).declaration.locals := by
  simp [Declaration.frame, checked.parameters, Value.zero, List.map_map, Function.comp_def]

private theorem condition_found (checked : seq.Checked mode program memory calls base outer args source)
    {stack : List Value} {result : Option NumType} {index : LocalIdx}
    {left right tail : Source H} {labels : List (OpenLabel H)}
    (ready : seq.SourceReady mode program memory calls labels stack (.ifThen result index left right tail) source) :
    ∃ bits : BitVec 32, (active).locals[index.toNat]? = some (.int .i32 bits) := by
  have typed := ready.2.2.2
  simp only [checkSourceAt, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  have localType := typed.2.1
  rw [← locals_typed checked, List.getElem?_map] at localType
  generalize lookup : (active).locals[index.toNat]? = value at localType
  cases value with
  | none => simp at localType
  | some v =>
    have same : v.type = .int .i32 := by simpa using localType
    rcases v with ⟨type, bits⟩
    cases same
    exact ⟨bits, rfl⟩

private theorem stack_types_i32 (saved : List Value) (bits : BitVec 32) :
    Prefix.stackTypes (saved ++ [Value.int .i32 bits]) = .int .i32 :: Prefix.stackTypes saved := by
  simp [Prefix.stackTypes, Value.int]

private theorem branch_test_checked {saved : List Value} {condition : BitVec 32} {branch : ForwardBranch}
    {tail : Source H} {labels : List (OpenLabel H)}
    (ready : seq.SourceReady mode program memory calls labels (saved ++ [Value.int .i32 condition]) (.brIf branch tail) source) :
    Graph.checkBranch (OpenLabel.targets (rootFn) labels) (Prefix.stackTypes saved) branch.depth branch.results = true ∧
      seq.SourceReady mode program memory calls labels saved tail source := by
  obtain ⟨scopes, allowed, listed, typed⟩ := ready
  have checks : checkForward (Prefix.stackTypes saved) (OpenLabel.targets (rootFn) labels) branch = true ∧
      seq.checkSourceAt (Prefix.stackTypes saved) (OpenLabel.results (rootFn) labels)
        (OpenLabel.targets (rootFn) labels) (OpenLabel.needsResume labels) tail = true := by
    rw [checkSourceAt, stack_types_i32] at typed
    exact Bool.and_eq_true_iff.mp typed
  exact ⟨checks.1, scopes, allowed, listed, checks.2⟩

private theorem table_target_checked {saved : List Value} {selector : BitVec 32} {table : ForwardTable}
    {labels : List (OpenLabel H)}
    (ready : seq.SourceReady mode program memory calls labels (saved ++ [Value.int .i32 selector]) (.brTable table) source) :
    Graph.checkBranch (OpenLabel.targets (rootFn) labels) (Prefix.stackTypes saved)
      (table.select selector).depth table.results = true := by
  have typed := ready.2.2.2
  rw [checkSourceAt, checkTable, stack_types_i32] at typed
  have checked := Bool.and_eq_true_iff.mp typed
  change checkForward (Prefix.stackTypes saved) (OpenLabel.targets (rootFn) labels) (table.select selector) = true
  cases found : table.depths[selector.toNat]? with
  | none => simpa [ForwardTable.select, found] using checked.1
  | some depth =>
    have member : depth ∈ table.depths := List.mem_of_getElem? found
    simpa [ForwardTable.select, found] using List.all_eq_true.mp checked.2 depth member

private theorem branch_outer_ready {stack : List Value} {branch : ForwardBranch}
    {label : OpenLabel H} {rest : List (OpenLabel H)}
    (positive : 0 < branch.depth.toNat)
    (typed : Graph.checkBranch (OpenLabel.targets (rootFn) (label :: rest)) (Prefix.stackTypes stack)
      branch.depth branch.results = true) :
    Graph.checkBranch (OpenLabel.targets (rootFn) rest) (Prefix.stackTypes (label.saved ++ stack))
      (lowerLabel branch.depth) branch.results = true := by
  obtain ⟨found, payload⟩ := decide_eq_true_eq.mp typed
  refine decide_eq_true_eq.mpr ⟨?_, ?_⟩
  · change (label.branchTypes :: OpenLabel.targets (rootFn) rest)[branch.depth.toNat]? = some branch.results at found
    change (OpenLabel.targets (rootFn) rest)[branch.depth.toNat - 1]? = some branch.results
    cases depth : branch.depth.toNat with
    | zero => simp [depth] at positive
    | succ n => simpa [depth] using found
  · have enough : branch.results.length ≤ (Prefix.stackTypes stack).length := by
      have count := congrArg List.length payload
      simp only [List.length_take, List.length_reverse] at count
      omega
    have ordered : Prefix.stackTypes (label.saved ++ stack) =
        Prefix.stackTypes stack ++ Prefix.stackTypes label.saved := by simp [Prefix.stackTypes]
    rw [ordered, List.take_append_of_le_length enough]
    exact payload

private theorem branch_payload_typed {extra payload : List Value} {target results : List NumType}
    {remaining : List (List NumType)}
    (count : payload.length = target.length)
    (typed : Graph.checkBranch (target :: remaining) (Prefix.stackTypes (extra ++ payload)) ⟨0⟩ results = true) :
    payload.map Value.type = target := by
  obtain ⟨found, suffix⟩ := decide_eq_true_eq.mp typed
  change some target = some results at found
  have types := (Option.some.inj found).symm
  subst results
  have countTypes : (Prefix.stackTypes payload).length = target.length := by simpa [Prefix.stackTypes] using count
  rw [← countTypes] at suffix
  simpa [Prefix.stackTypes] using suffix

private theorem function_branch_step {bytes : ByteArray} {stack : List Value} {branch : ForwardBranch}
    {skipped : List Admin} {dst : Config H} :
    Step host (renderPhase (.branching bytes stack branch skipped [])) dst ↔
      (∃ extra payload, stack = extra ++ payload ∧ payload.length = arity ∧ branch.depth.toNat = 0 ∧
        dst = ⟨live bytes, outer, seq.afterLabel args [] (values payload)⟩) ∨
      (0 < branch.depth.toNat ∧ dst = ⟨live bytes, outer,
        seq.afterLabel args [] (values stack ++ [.source (.br (lowerLabel branch.depth))])⟩) :=
  by simpa only [expression, List.map_nil, List.append_nil] using!
    (@framed_branch_iff H host (live bytes) outer active arity [] stack branch.depth skipped dst)

theorem function_branch_typed {bytes : ByteArray} {stack : List Value} {results : List NumType}
    {skipped : List Admin} {dst : Config H}
    (ready : seq.Ready mode program memory calls initial (.branching bytes stack ⟨⟨0⟩, results⟩ skipped []) source) :
    Step host (renderPhase (.branching bytes stack ⟨⟨0⟩, results⟩ skipped [])) dst ↔
      ∃ extra payload, stack = extra ++ payload ∧ payload.map Value.type = seq.root.function.declaration.results ∧
        dst = ⟨live bytes, outer, seq.afterLabel args [] (values payload)⟩ := by
  rw [function_branch_step]
  constructor
  · rintro (⟨extra, payload, rfl, count, _, eq⟩ | ⟨positive, _⟩)
    · exact ⟨extra, payload, rfl, branch_payload_typed count ready.2.1, eq⟩
    · exact (Nat.not_lt_zero _ positive).elim
  · rintro ⟨extra, payload, split, types, eq⟩
    exact .inl ⟨extra, payload, split, by simpa using congrArg List.length types, rfl, eq⟩

theorem preserves (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size start)
    (contract : seq.Contract host mode memory initial base source) {src dst : Phase H}
    (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src source) :
    seq.Ready mode program memory calls initial dst source := by
  cases edge with
  | resolve => exact ready
  | enter =>
    cases ready
    exact begin_ready checked extent ⟨trivial, checked.guardedBody, fun _ used => used, checked.typedBody⟩
  | openLoop =>
    obtain ⟨liveExtent, scopes, allowed, listed, typed⟩ := ready
    simp only [checkSourceAt, Bool.and_eq_true_iff] at typed
    have bodyListed : ∀ site ∈ seq.sourceSites _, site ∈ seq.sourceSites source :=
      fun site used => listed site (List.mem_append_left _ used)
    exact begin_ready checked liveExtent
      ⟨⟨typed.1, allowed.1, fun site used => listed site (List.mem_append_right _ used), scopes,
          allowed.2, bodyListed, typed.2⟩,
        allowed.2, bodyListed, typed.2⟩
  | openBlock =>
    obtain ⟨liveExtent, scopes, allowed, listed, typed⟩ := ready
    simp only [checkSourceAt, Bool.and_eq_true_iff] at typed
    exact begin_ready checked liveExtent
      ⟨⟨typed.1, allowed.1, fun site used => listed site (List.mem_append_right _ used), scopes, trivial⟩,
        allowed.2, fun site used => listed site (List.mem_append_left _ used), typed.2⟩
  | readCondition _ => exact ready
  | @select bytes stack result index left right tail condition labels =>
    obtain ⟨liveExtent, scopes, allowed, listed, typed⟩ := ready
    simp only [checkSourceAt, Bool.and_eq_true_iff] at typed
    by_cases zero : condition = 0
    · rw [ite_eq_left zero]
      refine ⟨liveExtent, scopes, ⟨allowed.1, allowed.2.2⟩, ?_, Bool.and_eq_true_iff.mpr ⟨typed.1, typed.2.2.2⟩⟩
      intro site used
      rcases List.mem_append.mp used with chosen | following
      · exact listed site (List.mem_append_left _ (List.mem_append_right _ chosen))
      · exact listed site (List.mem_append_right _ following)
    · rw [ite_eq_right zero]
      refine ⟨liveExtent, scopes, ⟨allowed.1, allowed.2.1⟩, ?_, Bool.and_eq_true_iff.mpr ⟨typed.1, typed.2.2.1⟩⟩
      intro site used
      rcases List.mem_append.mp used with chosen | following
      · exact listed site (List.mem_append_left _ (List.mem_append_left _ chosen))
      · exact listed site (List.mem_append_right _ following)
  | closeLabel _ =>
    obtain ⟨liveExtent, types, typed, allowed, listed, scopes, _⟩ := ready
    exact begin_ready checked liveExtent ⟨scopes, allowed, listed, by simpa [Prefix.stackTypes, types] using typed⟩
  | branchZero => exact begin_ready checked ready.1 (branch_test_checked ready.2).2
  | branchNonzero _ => exact ⟨ready.1, (branch_test_checked ready.2).1, ready.2.1⟩
  | selectTable => exact ⟨ready.1, table_target_checked ready.2, ready.2.1⟩
  | branchOuter positive => exact ⟨ready.1, branch_outer_ready positive ready.2.1, ready.2.2.2.2.2.1⟩
  | @branchExit bytes extra payload results skipped saved result tail rest count =>
    obtain ⟨liveExtent, typed, tailTyped, allowed, listed, scopes, _⟩ := ready
    have types := branch_payload_typed (target := result.toList)
      (remaining := OpenLabel.targets (rootFn) rest) count typed
    exact begin_ready checked liveExtent ⟨scopes, allowed, listed, by simpa [Prefix.stackTypes, types, OpenLabel.result, OpenLabel.saved, OpenLabel.tail] using tailTyped⟩
  | restartLoop =>
    obtain ⟨liveExtent, _, tailTyped, tailAllowed, tailListed, scopes, bodyAllowed, bodyListed, bodyTyped⟩ := ready
    exact ⟨liveExtent, scopes, ⟨tailAllowed, bodyAllowed⟩,
      fun site used => (List.mem_append.mp used).elim (bodyListed site) (tailListed site),
      Bool.and_eq_true_iff.mpr ⟨tailTyped, bodyTyped⟩⟩
  | branchFunction _ => exact ⟨ready.1, frame_allowed checked (RunProofs.values_allowed _)⟩
  | numeric moved =>
    obtain ⟨current, listed, later, check, scopes⟩ := ready
    have locals := locals_typed checked
    refine ⟨current, listed, later, ?_, scopes⟩
    rw [← locals]
    exact check_prefix_preserves (locals.symm ▸ check) moved
  | prefixTrap _ => exact ⟨ready.1, ready.2.2.2.2.1⟩
  | discard _ => exact ready
  | @closeTrap bytes labels =>
    obtain ⟨liveExtent, scopes⟩ := ready
    have graph (plain : OpenLabel.needsResume labels = false) :
        seq.Ready mode program memory calls initial (.graph ⟨bytes, outer, seq.afterLabel args labels [.trap]⟩) source :=
      ⟨liveExtent, frame_allowed checked (insert_allowed checked scopes plain
        (RunProofs.single_allowed.mpr .trap))⟩
    cases labels with
    | nil => exact graph rfl
    | cons label rest =>
      cases h : OpenLabel.needsResume (label :: rest) with
      | false => simpa only [closeTrapped, h, Bool.false_eq_true, ↓reduceIte] using graph h
      | true => simpa only [closeTrapped, h, ↓reduceIte] using
          (show seq.Ready mode program memory calls initial (.trapped bytes label.saved (seq.tailCode label) rest)
            source from ⟨liveExtent, scopes.2.2.2.1⟩)
  | hostResolve typed =>
    obtain ⟨current, listed, later, check, scopes⟩ := ready
    exact ⟨current, listed, later, typed, check_prefix_resume check typed, scopes⟩
  | returned behavior stored =>
    obtain ⟨next, discovered, _, _, _, readyNext⟩ := return_ready checked layout contract ready behavior
    exact (bytes_unique layout (discovered.symm.trans stored)) ▸ readyNext
  | diverged _ => exact ready
  | graph moved => exact moved.ready graphChecked ready

private theorem sound (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    {src dst : Phase H} (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src source) :
    Step host (renderPhase src) (renderPhase dst) := by
  cases edge with
  | resolve => exact (root_call checked).mpr rfl
  | enter =>
    cases ready
    exact (enter_step checked).mpr rfl
  | openLoop => exact loop_entry.mpr rfl
  | openBlock => exact block_entry.mpr rfl
  | readCondition found => exact (condition_step found).mpr rfl
  | select => exact select_step.mpr rfl
  | closeLabel _ => exact close_label_step.mpr rfl
  | branchZero => exact branch_test_step.mpr (ite_eq_left (rfl : (0 : BitVec 32) = 0) ▸ rfl)
  | branchNonzero nonzero => exact branch_test_step.mpr (ite_eq_right nonzero ▸ rfl)
  | selectTable => exact table_select_step.mpr rfl
  | branchOuter positive => exact branch_step.mpr (.inr ⟨positive, rfl⟩)
  | branchExit count => exact branch_step.mpr (.inl ⟨_, _, rfl, count, rfl, rfl⟩)
  | restartLoop => exact loop_restart_step.mpr rfl
  | branchFunction types =>
    exact (function_branch_typed ready).mpr ⟨_, _, rfl, types, rfl⟩
  | numeric moved => exact numeric_step.mpr (.inl ⟨_, moved, rfl⟩)
  | prefixTrap moved => exact numeric_step.mpr (.inr ⟨_, moved, rfl⟩)
  | discard moved => exact trap_step.mpr (.inl ⟨_, _, moved, rfl⟩)
  | closeTrap => exact trap_step.mpr (.inr ⟨rfl, rfl, rfl⟩)
  | hostResolve _ => exact (host_call (checked.linkedHosts _ ready.2.1)).mpr rfl
  | returned behavior stored =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr
      (.inl ⟨_, _, behavior, (render_delivered _).trans (by cases stored; rfl)⟩)
  | diverged behavior =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr (.inr ⟨behavior, rfl⟩)
  | graph moved =>
    exact Step.of_internal ((v1_step_iff_at graphChecked layout matched ready).mpr
      ⟨_, moved, moved.ready graphChecked ready, rfl⟩)

private theorem readback (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (contract : seq.Contract host mode memory initial base source)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src source) {dst : Config H}
    (step : Step host (renderPhase src) dst) :
    ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧ dst = renderPhase next := by
  cases src with
  | call current => exact ⟨_, .resolve, (root_call checked).mp step⟩
  | invoke current =>
    cases ready
    exact ⟨_, .enter, (enter_step checked).mp step⟩
  | loop => exact ⟨_, .openLoop, loop_entry.mp step⟩
  | block => exact ⟨_, .openBlock, block_entry.mp step⟩
  | if_ =>
    obtain ⟨bits, found⟩ := condition_found checked ready.2
    exact ⟨_, .readCondition found, (condition_step found).mp step⟩
  | test => exact ⟨_, .select, select_step.mp step⟩
  | completed =>
    exact ⟨_, .closeLabel (by simpa using congrArg List.length ready.2.1), close_label_step.mp step⟩
  | branchTest bytes stack branch fallthrough labels =>
    have checkedTest := ready.2.2.2.2
    simp only [checkSourceAt] at checkedTest
    obtain ⟨saved, condition, split, _⟩ := Memory32.split_i32 checkedTest
    subst stack
    have selected := branch_test_step.mp step
    by_cases zero : condition = 0
    · rw [ite_eq_left zero] at selected
      subst condition
      exact ⟨_, .branchZero, selected⟩
    · rw [ite_eq_right zero] at selected
      exact ⟨_, .branchNonzero zero, selected⟩
  | tableSelect bytes stack table labels =>
    have checkedSelector := ready.2.2.2.2
    simp only [checkSourceAt, checkTable] at checkedSelector
    obtain ⟨saved, selector, rfl, _⟩ := Memory32.split_i32 checkedSelector
    exact ⟨_, .selectTable, table_select_step.mp step⟩
  | branching bytes stack branch skipped labels =>
    cases labels with
    | nil =>
      have found : (rootFn).entryLabels[branch.depth.toNat]? = some branch.results :=
        (decide_eq_true_eq.mp ready.2.1).1
      have bound := List.getElem?_eq_some_iff.mp found
      have zero : branch.depth.toNat = 0 := by simpa [Function.entryLabels] using bound.1
      rcases branch with ⟨depth, results⟩
      have same : depth = ⟨0⟩ := Idx.toNat_injective zero
      subst depth
      obtain ⟨extra, payload, rfl, types, eq⟩ := (function_branch_typed ready).mp step
      exact ⟨_, .branchFunction types, eq⟩
    | cons label rest =>
      rcases branch_step.mp step with ⟨extra, payload, rfl, count, zero, eq⟩ | ⟨positive, eq⟩
      · rcases branch with ⟨depth, results⟩
        have same : depth = ⟨0⟩ := Idx.toNat_injective zero
        subst depth
        cases label with
        | block => exact ⟨_, .branchExit count, eq⟩
        | loop => exact ⟨_, .restartLoop, eq⟩
      · exact ⟨_, .branchOuter positive, eq⟩
  | computing bytes stack remaining site later labels nextSource =>
    cases remaining with
    | nil =>
      obtain ⟨saved, actual, rfl, typed, _⟩ := check_prefix_arguments ready.2.2.2.1
      exact ⟨_, .hostResolve typed, (host_call (checked.linkedHosts _ ready.2.1)).mp step⟩
    | cons op rest =>
      rcases numeric_step.mp step with ⟨next, moved, eq⟩ | ⟨saved, trapped, eq⟩
      · exact ⟨_, .numeric moved, eq⟩
      · exact ⟨_, .prefixTrap trapped, eq⟩
  | trapped bytes saved tail labels =>
    rcases trap_step.mp step with ⟨kept, rest, discarded, eq⟩ | ⟨rfl, rfl, eq⟩
    · exact ⟨_, .discard discarded, eq⟩
    · exact ⟨_, .closeTrap, eq⟩
  | pending bytes saved actual site later labels nextSource =>
    have ⟨_, listed, _, arguments, _⟩ := ready
    rcases (pending_step (checked.linkedHosts site listed) arguments).mp step with
      ⟨after, r, returned, eq⟩ | ⟨diverged, eq⟩
    · obtain ⟨next, stored, _, _, _, _⟩ := return_ready checked layout contract ready returned
      refine ⟨_, .returned returned stored, ?_⟩
      rw [render_delivered]
      rw [stored] at eq
      exact eq
    · exact ⟨_, .diverged diverged, eq⟩
  | graph state =>
    have internal := (ReadyFor.internal_iff layout ready).mp step
    obtain ⟨next, moved, _, eq⟩ := (v1_step_iff_at graphChecked layout matched ready).mp internal
    exact ⟨.graph next, .graph moved, eq⟩

theorem step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base source)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src source) {dst : Config H} :
    Step host (renderPhase src) dst ↔
      ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next source ∧ dst = renderPhase next := by
  constructor
  · intro step
    obtain ⟨next, moved, eq⟩ := readback graphChecked checked layout matched contract ready step
    exact ⟨next, moved, preserves graphChecked checked layout extent contract moved ready, eq⟩
  · rintro ⟨next, moved, _, rfl⟩
    exact sound graphChecked checked layout matched moved ready

private theorem closed_trapped_phase (bytes : ByteArray) (labels : List (OpenLabel H)) :
    (∃ saved tail scopes, seq.closeTrapped outer args bytes labels = .trapped bytes saved tail scopes) ∨
      ∃ state, seq.closeTrapped outer args bytes labels = .graph state := by
  cases labels with
  | nil => exact .inr ⟨_, rfl⟩
  | cons label rest =>
    simp only [closeTrapped]
    split
    · exact .inl ⟨_, _, _, rfl⟩
    · exact .inr ⟨_, rfl⟩

theorem trapped_run {bytes : ByteArray} {saved : List Value} {tail : List Admin} {labels : List (OpenLabel H)} {dst : Phase H}
    (run : seq.Runs host mode program memory base initial start outer args (.trapped bytes saved tail labels) dst) :
    (∃ saved rest scopes, dst = .trapped bytes saved rest scopes) ∨ ∃ state, dst = .graph state := by
  induction run with
  | refl => exact .inl ⟨saved, tail, labels, rfl⟩
  | tail _ transition ih =>
    rcases ih with ⟨saved, rest, scopes, rfl⟩ | ⟨state, rfl⟩
    · cases transition with
      | discard _ => exact .inl ⟨_, _, _, rfl⟩
      | closeTrap => exact closed_trapped_phase bytes scopes
    · cases transition with
      | graph _ => exact .inr ⟨_, rfl⟩

theorem run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args source)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base source)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src source) {dst : Config H} :
    Steps host (renderPhase src) dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next source ∧ dst = renderPhase next :=
  HostEntry.Proofs.finite_run_iff renderPhase _ _
    (fun {_ _} h => step_iff graphChecked checked layout matched extent contract h)
    (fun step h => preserves graphChecked checked layout extent contract step h) ready

end Execution
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs
