module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (Result Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

theorem get_typed {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {args stack : List Value} {i : LocalIdx}
    {ops : List Graph.Memory32.Op} (argsTyped : args.map Value.type = callee.fn.declaration.params)
    (typed : Typed callee types labels stack (.ranked (.numeric (.get i)) :: ops)) :
    ∃ v, (callee.fn.declaration.frame args).locals[i.toNat]? = some v ∧
      Typed callee types labels (stack ++ [v]) ops := by
  have locals : (callee.fn.declaration.frame args).locals.map Value.type =
      callee.fn.declaration.params ++ callee.fn.declaration.locals := by
    simp [Declaration.frame, List.map_map, Function.comp_def, Value.zero, argsTyped]
  unfold Typed at typed
  simp only [Graph.Memory32.Function.checkRegion, Graph.Memory32.Function.checkRegionOp,
    Graph.checkOp, Prefix.checkOp] at typed
  rw [← locals, List.getElem?_map] at typed
  cases found : (callee.fn.declaration.frame args).locals[i.toNat]? with
  | none => simp [found] at typed
  | some v =>
    exact ⟨v, rfl, by
      simpa [found, Typed,
        Prefix.stackTypes, List.reverse_append] using typed⟩

theorem typed_nil {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {stack : List Value} (typed : Typed callee types labels stack []) :
    resultTyped types (.values stack) := by
  simpa [Typed,
    Graph.Memory32.Function.checkRegion, Prefix.stackTypes, resultTyped] using typed

private theorem resume_typed {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {saved operands : List Value}
    {params results : List NumType} {rest : List Graph.Memory32.Op}
    (arguments : operands.map Value.type = params)
    (resume : callee.fn.checkRegion (results.reverse ++ (Prefix.stackTypes (saved ++ operands)).drop params.length) types rest labels = true)
    (vs : List Value) (typed : vs.map Value.type = results) : Typed callee types labels (saved ++ vs) rest := by
  have count : params.reverse.length = params.length := List.length_reverse
  have kept : (params.reverse ++ Prefix.stackTypes saved).drop params.length = Prefix.stackTypes saved := by
    rw [← count, List.drop_left]
  simp only [Prefix.stackTypes] at kept
  simpa only [Typed, Prefix.stackTypes, List.map_append,
    List.reverse_append, arguments, typed, kept] using resume

theorem call_typed {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {stack : List Value} {target : CallTarget}
    {ops : List Graph.Memory32.Op} (typed : Typed callee types labels stack (.ranked (.call target) :: ops)) :
    ∃ saved operands, stack = saved ++ operands ∧ operands.map Value.type = target.declaration.params ∧
      target ∈ callee.fn.targets ∧
      ∀ vs : List Value, vs.map Value.type = target.declaration.results → Typed callee types labels (saved ++ vs) ops := by
  change (decide (target ∈ callee.fn.targets ∧
    (Prefix.stackTypes stack).take target.declaration.params.length = target.declaration.params.reverse) &&
    callee.fn.checkRegion (target.declaration.results.reverse ++
      (Prefix.stackTypes stack).drop target.declaration.params.length) types ops labels) = true at typed
  obtain ⟨guard, resume⟩ := Bool.and_eq_true_iff.mp typed
  obtain ⟨used, suffix⟩ := of_decide_eq_true guard
  obtain ⟨saved, operands, rfl, arguments⟩ := Graph.SuffixTyped.split suffix
  exact ⟨saved, operands, rfl, arguments, used, resume_typed arguments resume⟩

private theorem direct_resume {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {saved operands : List Value} {target : CallTarget}
    {rest : List Graph.Memory32.Op} (typed : operands.map Value.type = target.declaration.params)
    (checked : Typed callee types labels (saved ++ operands) (.ranked (.call target) :: rest)) :
    ∀ vs : List Value, vs.map Value.type = target.declaration.results → Typed callee types labels (saved ++ vs) rest := by
  obtain ⟨kept, used, split, usedTyped, _, resume⟩ := call_typed checked
  have count : used.length = operands.length := by
    simpa using congrArg List.length (usedTyped.trans typed.symm)
  obtain ⟨rfl, _⟩ := List.append_inj' split count.symm
  exact resume

theorem indirect_typed {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {stack : List Value} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {rest : List Graph.Memory32.Op}
    (typed : Typed callee types labels stack (.callIndirect index signature :: rest)) :
    ∃ (saved operands : List Value) (selector : BitVec 32), stack = (saved ++ operands) ++ [Value.int .i32 selector] ∧
      operands.map Value.type = signature.params ∧
      ∀ vs : List Value, vs.map Value.type = signature.results → Typed callee types labels (saved ++ vs) rest := by
  obtain ⟨stack, selector, rfl, suffix, resume⟩ := Graph.Memory32.Function.indirect_typed typed
  obtain ⟨saved, operands, rfl, arguments⟩ := Graph.SuffixTyped.split suffix
  exact ⟨saved, operands, selector, rfl, arguments, resume_typed arguments resume⟩

private theorem indirect_resume {callee : MemoryTarget} {types : List NumType} {labels : List (List NumType)} {saved operands : List Value} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {selector : BitVec 32} {rest : List Graph.Memory32.Op}
    (typed : operands.map Value.type = signature.params)
    (checked : Typed callee types labels ((saved ++ operands) ++ [Value.int .i32 selector])
      (.callIndirect index signature :: rest)) :
    ∀ vs : List Value, vs.map Value.type = signature.results → Typed callee types labels (saved ++ vs) rest := by
  obtain ⟨kept, used, _, split, usedTyped, resume⟩ := indirect_typed checked
  obtain ⟨split, _⟩ := List.append_inj' split (by simp)
  have count : used.length = operands.length := by
    simpa using congrArg List.length (usedTyped.trans typed.symm)
  obtain ⟨rfl, _⟩ := List.append_inj' split count.symm
  exact resume

theorem after_child_render {H : Type} (arity : Nat) (parent child : MemoryTarget) (args saved : List Value)
    (rest : List Graph.Memory32.Op) (phase : Phase H) :
    renderAt parent arity (afterChild args saved child rest phase) =
      [.frame arity (parent.fn.declaration.frame args)
        [.label arity [] (values saved ++ render child phase ++ code rest)]] := by
  cases phase <;> try rfl
  case done out =>
    cases out <;>
      simp [afterChild, renderUnder, frameCode, result, values_append, List.append_assoc]

private theorem tail_supported {enabled : Bool} {explicitDepth : Nat} {op : Graph.Memory32.Op} {ops : List Graph.Memory32.Op}
    (checked : (op :: ops).all (MemoryTarget.supportedOpAt enabled explicitDepth) = true) :
    ops.all (MemoryTarget.supportedOpAt enabled explicitDepth) = true := by
  exact List.all_eq_true.mpr (fun a member => List.all_eq_true.mp checked a (List.mem_cons_of_mem _ member))

private theorem supportedCode_eq_all (enabled : Bool) (explicitDepth : Nat) (ops : List Graph.Memory32.Op) :
    MemoryTarget.supportedCodeAt enabled explicitDepth ops = ops.all (MemoryTarget.supportedOpAt enabled explicitDepth) := by
  induction ops <;> simp [MemoryTarget.supportedCodeAt, *]

theorem source_head (op : Graph.Memory32.Op) (rest : List Graph.Memory32.Op) :
    op ∈ MemoryTarget.sourceOps (op :: rest) := by simp [MemoryTarget.sourceOps]

private theorem tail_fromCode {callee : MemoryTarget} {op : Graph.Memory32.Op} {ops : List Graph.Memory32.Op}
    (linked : FromCode callee (op :: ops)) : FromCode callee ops :=
  fun _ member => linked (by simp [MemoryTarget.sourceOps, member])

inductive LabelSuccessor {H : Type} (args : List Value) : Phase H → Prop where
  | active {phase} (inside : InLabel args phase) : LabelSuccessor args phase
  | exit (out : Result) : LabelSuccessor args (.exit args out)
  | lowered (stack : List Value) (depth : LabelIdx) (result : List NumType) :
      LabelSuccessor args (.lowered args stack depth result)

theorem inLabel_next {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H} {site : IndirectSite}
    {callee : MemoryTarget} {bytes written : ByteArray} {args : List Value} {phase next : Phase H}
    (entered : InLabel args phase) (move : Edge mem host site callee bytes phase written next) :
    LabelSuccessor args next := by
  cases move <;> simp only [InLabel] at entered <;> try exact .active entered
  case brIf =>
    unfold afterBrIf
    split <;> exact .active entered
  case branchLower => cases entered; exact .lowered ..
  case branchDone => cases entered; exact .exit _
  case labelDone => cases entered; exact .exit _
  case labelTrap => cases entered; exact .exit _
  case child =>
    rename_i next rest move
    cases next with
    | done out => cases out <;> exact .active entered
    | _ => exact .active entered
  case armStep =>
    rename_i next rest active move
    cases next with
    | exit _ out => cases out <;> exact .active entered
    | _ => exact .active entered

theorem branch_result {types result : List NumType} {labels : List (List NumType)}
    {stack : List Value} (head : labels[0]? = some types)
    (typed : BranchTyped labels ⟨0⟩ result stack) : result = types :=
  Option.some.inj (typed.1.symm.trans head)

private theorem branch_lower {labels : List (List NumType)} {depth : LabelIdx}
    {result : List NumType} {stack : List Value} (positive : 0 < depth.toNat)
    (typed : BranchTyped labels depth result stack) :
    BranchTyped labels.tail (lowerLabel depth) result stack := by
  refine ⟨?_, typed.2⟩
  cases labels with
  | nil => cases typed.1
  | cons label labels =>
    cases depthEq : depth.toNat with
    | zero => omega
    | succ index =>
      have lowered : (lowerLabel depth).toNat = index := by
        change depth.toNat - 1 = index
        omega
      simpa only [depthEq, lowered, List.tail_cons, List.getElem?_cons_succ] using typed.1

private theorem branch_prepend {labels : List (List NumType)} {depth : LabelIdx}
    {result : List NumType} {stack : List Value} (saved : List Value)
    (typed : BranchTyped labels depth result stack) :
    BranchTyped labels depth result (saved ++ stack) := by
  refine ⟨typed.1, ?_⟩
  obtain ⟨scratch, payload, rfl, signature⟩ := Graph.SuffixTyped.split typed.2
  have count : result.reverse.length = result.length := List.length_reverse
  simp only [Graph.SuffixTyped, Prefix.stackTypes, List.map_append, List.reverse_append, signature, List.append_assoc]
  rw [← count, List.take_left]

theorem ready_step_at {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {host : HostSemantics H} {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (linked : site.MemoryLinked mem host .recursive) (registered : site.memoryLookup callee.address = some callee.fn)
    (move : Edge mem host site callee bytes phase written next)
    {types : List NumType} {labels : List (List NumType)}
    (label : (labels ++ callee.fn.entryLabels)[0]? = some types)
    (ready : ReadyAt mem host site callee types labels phase) : ReadyAt mem host site callee types labels next := by
  induction move generalizing types labels with
  | enter =>
    have checked := linked.checked _ registered
    obtain ⟨arguments, rfl, rfl⟩ := ready
    exact ⟨arguments, checked.supported, checked.body, fun _ member => member⟩
  | get found =>
    obtain ⟨v, lookup, typed⟩ := get_typed ready.1 ready.2.2.1
    rw [found] at lookup
    cases lookup
    exact ⟨ready.1, tail_supported ready.2.1, typed, tail_fromCode ready.2.2.2⟩
  | load _ =>
    obtain ⟨kept, address, split, typed⟩ := Graph.Memory32.Function.region_load_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed _, tail_fromCode ready.2.2.2⟩
  | store _ =>
    obtain ⟨kept, address, operand, split, typed⟩ := Graph.Memory32.Function.region_store_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed, tail_fromCode ready.2.2.2⟩
  | size =>
    exact ⟨ready.1, tail_supported ready.2.1, Graph.Memory32.Function.region_size_typed ready.2.2.1 _,
      tail_fromCode ready.2.2.2⟩
  | grow _ _ | growFail =>
    obtain ⟨kept, delta, split, typed⟩ := Graph.Memory32.Function.region_grow_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed _, tail_fromCode ready.2.2.2⟩
  | @call callee child bytes args saved operands target rest link typed =>
    have resume := direct_resume typed ready.2.2.1
    refine ⟨ready.1, link.registered, link.allocated, by simp, ?_,
      tail_supported ready.2.1, (tail_fromCode ready.2.2.2), ?_⟩
    · exact ⟨by simpa only [link.declaration] using typed, rfl, rfl⟩
    · simpa only [link.declaration] using resume
  | callHost link typed =>
    exact ⟨ready.1, link.allocated, typed, link.contract, tail_supported ready.2.1,
      (tail_fromCode ready.2.2.2), direct_resume typed ready.2.2.1⟩
  | @callIndirect callee child bytes args saved operands index signature selector rest lookup typed =>
    have resume := indirect_resume typed ready.2.2.1
    cases lookup with
    | memory _ found allocated signatureEq =>
      have params := congrArg (fun (ty : Wasm.Lime1.FuncType) => ty.params) signatureEq
      have results := congrArg (fun (ty : Wasm.Lime1.FuncType) => ty.results) signatureEq
      refine ⟨ready.1, found, allocated, by simp, ?_, tail_supported ready.2.1,
        (tail_fromCode ready.2.2.2), ?_⟩
      · exact ⟨typed.trans params.symm, rfl, rfl⟩
      · exact fun vs typed => resume vs (typed.trans results)
  | @callIndirectHost callee target bytes args saved operands index signature selector rest lookup typed =>
    have resume := indirect_resume typed ready.2.2.1
    cases lookup with
    | @host address hostCode entry allocated =>
      have link := linked.indirect callee registered index signature (ready.2.2.2 (source_head _ _))
      obtain ⟨fn, found, contract⟩ := link.entries address (List.mem_of_getElem? entry)
      change base.funcs[address.value]? = some (.host ⟨signature.params, signature.results⟩ hostCode)
        at allocated
      rw [allocated] at found
      cases found
      exact ⟨ready.1, allocated, typed, contract rfl, tail_supported ready.2.1,
        (tail_fromCode ready.2.2.2), resume⟩
  | hostReturned _ typed _ =>
    obtain ⟨argsTyped, _, _, _, supported, inCode, resume⟩ := ready
    exact ⟨argsTyped, supported, resume _ typed, inCode⟩
  | hostTrapped => exact ready.1
  | hostDiverged => exact ready
  | @brIf callee bytes args stack depth result rest guard =>
    obtain ⟨kept, condition, split, target, payload, resume⟩ :=
      Graph.Memory32.Function.br_if_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split (by simp)
    unfold afterBrIf
    split
    · exact ⟨ready.1, tail_supported ready.2.1, resume, tail_fromCode ready.2.2.2⟩
    · exact ⟨ready.1, target, payload⟩
  | branchDone typed => exact ⟨ready.1, typed.trans (branch_result label ready.2)⟩
  | branchLower positive => exact ⟨ready.1, branch_lower positive ready.2⟩
  | @ifSelect callee bytes args saved type left right rest guard =>
    obtain ⟨kept, condition, split, leftTyped, rightTyped, resume⟩ :=
      Graph.Memory32.Function.if_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split (by simp)
    have arms : MemoryTarget.supportedCodeAt mem.extent.growthEnabled (labels.length + 1) left = true ∧
        MemoryTarget.supportedCodeAt mem.extent.growthEnabled (labels.length + 1) right = true :=
      Bool.and_eq_true_iff.mp (List.all_eq_true.mp ready.2.1 (.if_ type left right) (List.mem_cons_self ..))
    change ReadyAt mem host site callee types labels (.ifBlock args saved type (selectArm guard left right) rest)
    by_cases zero : guard = (0 : BitVec 32)
    · have chosen : selectArm guard left right = right := ite_eq_left zero
      rw [chosen]
      exact ⟨ready.1, (supportedCode_eq_all _ _ _ ▸ arms.2), (fun _ member =>
        ready.2.2.2 (by simp [MemoryTarget.sourceOps, MemoryTarget.descendants, member])),
        rightTyped, tail_supported ready.2.1, tail_fromCode ready.2.2.2, resume⟩
    · have chosen : selectArm guard left right = left := ite_eq_right zero
      rw [chosen]
      exact ⟨ready.1, (supportedCode_eq_all _ _ _ ▸ arms.1), (fun _ member =>
        ready.2.2.2 (by simp [MemoryTarget.sourceOps, MemoryTarget.descendants, member])),
        leftTyped, tail_supported ready.2.1, tail_fromCode ready.2.2.2, resume⟩
  | ifEnter =>
    obtain ⟨argsTyped, supported, armSource, armTyped, tailSupported, tailSource, resume⟩ := ready
    exact ⟨argsTyped, rfl, ⟨argsTyped, supported, armTyped, armSource⟩, tailSupported, tailSource, resume⟩
  | @armStep callee bytes written args saved type phase next rest entered move ih =>
    obtain ⟨argsTyped, _, active, supported, inCode, resume⟩ := ready
    have advanced := ih registered rfl active
    cases inLabel_next entered move with
    | active inside =>
      cases next <;> first
        | exact ⟨argsTyped, inside, advanced, supported, inCode, resume⟩
        | change False at inside
          exact inside.elim
    | exit out =>
      cases out with
      | values vs => exact ⟨argsTyped, supported, resume vs advanced.2, inCode⟩
      | trap => exact argsTyped
    | lowered operands depth declared =>
      exact ⟨argsTyped, branch_prepend saved advanced.2⟩
  | @child callee child bytes written args saved phase next rest move ih =>
    obtain ⟨argsTyped, found, allocated, _, childReady, supported, inCode, resume⟩ := ready
    have after := ih found rfl childReady
    cases next <;> try exact ⟨argsTyped, found, allocated, by simp, after, supported, inCode, resume⟩
    case done out =>
      cases out with
      | trap => exact argsTyped
      | values vs => exact ⟨argsTyped, supported, resume vs after, inCode⟩
  | loadTrap | storeTrap | indirectTrap => exact ready.1
  | erase => exact ready
  | labelDone => exact ⟨ready.1, typed_nil ready.2.2.1⟩
  | labelTrap => exact ⟨ready, trivial⟩
  | frameDone => exact ready.2

theorem live_step {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {host : HostSemantics H} {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (move : Edge mem host site callee bytes phase written next) (live : mem.Live bytes) : mem.Live written := by
  induction move with
  | child _ ih | armStep _ _ ih => exact ih live
  | hostReturned nextLive _ _ | hostTrapped nextLive _ => exact nextLive
  | store write => exact mem.live_same_size live (MemoryWrite.closed_at write)
  | grow enabled edge => exact mem.live_grow enabled live edge
  | _ => exact live

theorem extent_mono {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (move : Edge mem Execution.Runtime.noHostCalls site callee bytes phase written next) : bytes.size ≤ written.size := by
  induction move with
  | child _ ih | armStep _ _ ih => exact ih
  | hostReturned _ _ answer | hostTrapped _ answer => exact answer.elim
  | store write => exact Nat.le_of_eq (MemoryWrite.closed_at write).symm
  | grow _ edge =>
    rw [MemoryGrow.grown_bytes edge]
    simp only [Memory32.current, ByteArray.size_append]
    exact Nat.le_add_right _ _
  | _ => exact Nat.le_refl _

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs
