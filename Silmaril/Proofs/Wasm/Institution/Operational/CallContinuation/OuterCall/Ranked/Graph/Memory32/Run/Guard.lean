module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame FuncAddr MemAddr ModuleInst Value)
open Wasm.V1.Execution

theorem append_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {l r : List Admin} :
    CodeAllowedFor mode p m calls rank mod (l ++ r) ↔ CodeAllowedFor mode p m calls rank mod l ∧ CodeAllowedFor mode p m calls rank mod r := by
  simp only [CodeAllowedFor, List.mem_append, or_imp, forall_and]

theorem single_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {x : Admin} :
    CodeAllowedFor mode p m calls rank mod [x] ↔ AllowedFor mode p m calls rank mod x := by
  simp [CodeAllowedFor]

theorem value_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (v : Value) :
    AllowedFor mode p m calls rank mod (value v) := by
  rcases v with ⟨t, bits⟩
  cases t with
  | int width => exact .source (.intConst width bits)
  | float width => exact .source (.floatConst width bits)

theorem values_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (vs : List Value) :
    CodeAllowedFor mode p m calls rank mod (values vs) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact value_allowed v

theorem source_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {i : Wasm.V1.Instr}
    (guard : AllowedFor mode p m calls rank mod (.source i)) : SourceAllowedFor mode p m calls rank mod i := by
  cases guard with | source h => exact h

mutual

private theorem code_sources {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {fn : Function} (links : ∀ target ∈ fn.targets, ∃ callee, p.lookup target.address = some callee ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧ calls.permits fn.rank callee.rank)
    (slot : fn.declaration.module.memories[0]? = some m) (code : List Op)
    (labels : List (List NumType))
    (supported : supportedCode code labels mode (p.checkIndirect calls fn.rank fn.declaration.module) = true)
    (targets : ∀ target ∈ codeTargets code, target ∈ fn.targets) :
    ∀ i ∈ v1Code code, SourceAllowedFor mode p m calls fn.rank fn.declaration.module i := by
  cases code with
  | nil => simp [v1Code]
  | cons op rest =>
    have checks := Bool.and_eq_true_iff.mp supported
    intro i hi
    simp only [v1Code, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact op_source links slot op labels checks.1
        (fun target used => targets target (List.mem_append_left _ used))
    · exact code_sources links slot rest labels checks.2
        (fun target used => targets target (List.mem_append_right _ used)) i hi

private theorem op_source {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {fn : Function} (links : ∀ target ∈ fn.targets, ∃ callee, p.lookup target.address = some callee ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧ calls.permits fn.rank callee.rank)
    (slot : fn.declaration.module.memories[0]? = some m) (op : Op)
    (labels : List (List NumType))
    (supported : op.supportedIn labels mode (p.checkIndirect calls fn.rank fn.declaration.module) = true)
    (targets : ∀ target ∈ op.targets, target ∈ fn.targets) :
    SourceAllowedFor mode p m calls fn.rank fn.declaration.module op.v1 := by
  cases op with
  | callIndirect index signature => exact .callIndirect supported
  | load offset => exact .load offset slot
  | store offset => exact .store offset slot
  | block result body =>
    exact .block (code_sources links slot body (result.toList :: labels) supported targets)
  | loop result body =>
    exact .loop (code_sources links slot body ([] :: labels) supported targets)
  | size | grow =>
    cases mode with
    | fixed => contradiction
    | growing maximum => first | exact .memorySize rfl slot | exact .memoryGrow rfl slot
  | if_ result left right =>
    have checks := Bool.and_eq_true_iff.mp supported
    exact .if_
      (code_sources links slot left (result.toList :: labels) checks.1
        (fun target used => targets target (List.mem_append_left _ used)))
      (code_sources links slot right (result.toList :: labels) checks.2
        (fun target used => targets target (List.mem_append_right _ used)))
  | ranked op =>
    cases op with
    | numeric op =>
      cases op with
      | get i => exact .get i
      | bin t bin => exact .bin t _
    | set idx => exact .set idx
    | tee idx => exact .tee idx
    | br depth _ => exact .br depth
    | brIf depth _ => exact .brIf depth
    | brTable depths fallback _ => exact .brTable depths fallback
    | unreachable => exact .unreachable
    | return_ => exact .return_
    | call target =>
      have uses : target ∈ fn.targets := targets target (List.Mem.head _)
      obtain ⟨callee, h, resolved, permitted⟩ := links target uses
      exact .call resolved h permitted
    | _ => contradiction

end

theorem tail_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {fn : Function} (links : ∀ target ∈ fn.targets, ∃ callee, p.lookup target.address = some callee ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧ calls.permits fn.rank callee.rank)
    (slot : fn.declaration.module.memories[0]? = some m)
    (supported : supportedCode fn.code fn.entryLabels mode
      (p.checkIndirect calls fn.rank fn.declaration.module) = true) :
    CodeAllowedFor mode p m calls fn.rank fn.declaration.module (expression (v1Code fn.code)) := by
  intro admin member
  obtain ⟨i, used, rfl⟩ := List.mem_map.mp member
  exact .source (code_sources links slot fn.code fn.entryLabels supported
    (fun target h => by
      have targets : ∀ code, codeTargets code = code.flatMap Op.targets := by
        intro code
        induction code <;> simp_all [codeTargets]
      simpa [targets, Function.targets] using h) i used)

theorem body_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} (checked : p.checkV1 m mode calls = true)
    {a : FuncAddr} {fn : Function} (found : p.lookup a = some fn) :
    CodeAllowedFor mode p m calls fn.rank fn.declaration.module (expression fn.v1Func.body) := by
  obtain ⟨_, supported, _, slot⟩ := p.function_checked checked found
  rw [fn.body_expression, append_allowed]
  refine ⟨values_allowed _, ?_⟩
  intro x member
  obtain ⟨op, used, rfl⟩ := List.mem_map.mp member
  have links (target : CallTarget) (uses : target ∈ fn.targets) :
      ∃ callee, p.lookup target.address = some callee ∧
        fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧ calls.permits fn.rank callee.rank := by
    obtain ⟨callee, present, resolved, _, permitted⟩ := p.linked_target checked found uses
    exact ⟨callee, present, resolved, permitted⟩
  exact .source (op_source links slot op fn.entryLabels (List.all_eq_true.mp supported op used)
    (fun target h => List.mem_flatMap.mpr ⟨op, used, h⟩))

private theorem expression_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {code : Wasm.V1.Expr} (guard : ∀ i ∈ code, SourceAllowedFor mode p m calls rank mod i) :
    CodeAllowedFor mode p m calls rank mod (expression code) := by
  intro x member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  exact .source (guard i hi)

theorem pure_allowed {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {before after : List Admin} (move : PureStep before after)
    (guard : CodeAllowedFor mode p m calls rank mod before) : CodeAllowedFor mode p m calls rank mod after := by
  cases move with
  | block result body =>
    have h := source_allowed (guard _ (List.Mem.head _))
    cases h with
    | block bodyGuard =>
      exact single_allowed.mpr (.label (by cases result <;> simp) (expression_allowed bodyGuard))
  | loop =>
    have h := source_allowed (guard _ (List.Mem.head _))
    cases h with
    | loop bodyGuard => exact single_allowed.mpr (.loopLabel (.loop bodyGuard) (expression_allowed bodyGuard))
  | ifZero =>
    have h := source_allowed (guard _ (List.Mem.tail _ (List.Mem.head _)))
    cases h with | if_ _ right => exact single_allowed.mpr (.source (.block right))
  | ifNonzero =>
    have h := source_allowed (guard _ (List.Mem.tail _ (List.Mem.head _)))
    cases h with | if_ left _ => exact single_allowed.mpr (.source (.block left))
  | brIfNonzero depth _ _ =>
    exact single_allowed.mpr (.source (.br depth))
  | brTable depths fallback selector =>
    exact single_allowed.mpr (.source (.br (depths[selector.toNat]?.getD fallback)))
  | labelBranch n cont extra vs tail arity =>
    cases (single_allowed.mp guard) with
    | label _ _ => exact append_allowed.mpr ⟨values_allowed vs, values_allowed []⟩
    | loopLabel restart _ => exact append_allowed.mpr ⟨values_allowed vs, single_allowed.mpr (.source restart)⟩
  | labelBranchOuter n cont vs tail idx outer =>
    exact append_allowed.mpr ⟨values_allowed _, single_allowed.mpr (.source (.br (lowerLabel idx)))⟩
  | labelReturn n cont vs tail =>
    apply append_allowed.mpr
    exact ⟨values_allowed _, single_allowed.mpr (.source .return_)⟩
  | localTee i v =>
    change CodeAllowedFor mode p m calls rank mod (values [v, v] ++ [.source (.localSet i)])
    exact append_allowed.mpr ⟨values_allowed _, single_allowed.mpr (.source (.set i))⟩
  | _ =>
    first
    | exact values_allowed _
    | exact values_allowed []
    | exact single_allowed.mpr (value_allowed _)
    | exact single_allowed.mpr .trap

theorem edge_module {mode : MemoryMode} {p : Program} {m : MemAddr} {src dst : State} (move : EdgeAt mode p m src dst) :
    dst.frame.module = src.frame.module := by
  induction move <;> first | rfl | assumption

private theorem extent_of_size_eq {mode : MemoryMode} {minimum : Nat} {before after : ByteArray}
    (sizes : after.size = before.size) (extent : mode.extent minimum before) :
    mode.extent minimum after := by
  cases mode <;> simpa only [MemoryMode.extent, BoundedExtent, MemoryGrow.SizeAllows, Execution.Memory.size, sizes] using extent

theorem extent_preserved {mode : MemoryMode} {p : Program} {m : MemAddr} {src dst : State} {minimum : Nat}
    (move : EdgeAt mode p m src dst) (extent : mode.extent minimum src.bytes) : mode.extent minimum dst.bytes := by
  induction move with
  | grow enabled _ rule =>
    cases enabled
    exact BoundedExtent.grow extent rule
  | store _ rule => exact extent_of_size_eq (MemoryWrite.closed_at rule) extent
  | _ => first | exact extent | exact ‹_ → _› extent

theorem extent_mono {mode : MemoryMode} {p : Program} {m : MemAddr} {src dst : State}
    (move : EdgeAt mode p m src dst) : src.bytes.size ≤ dst.bytes.size := by
  induction move with
  | @grow bytes _ maximum delta grown _ _ rule =>
    change bytes.size ≤ grown.size
    cases MemoryGrow.invert rule with
    | grow _ _ ok =>
      rw [Execution.Memory.grow_size _ _ _ _ ok]
      exact Nat.le_add_right _ _
  | @store bytes _ _ _ _ written _ rule =>
    exact (show written.size = bytes.size from MemoryWrite.closed_at rule).symm.le
  | _ => first | assumption | exact Nat.le_refl _

theorem preserve {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} (checked : p.checkV1 m mode calls = true)
    {src dst : State} (move : EdgeAt mode p m src dst) {rank : Nat}
    (ready : CodeAllowedFor mode p m calls rank src.frame.module src.code) :
    CodeAllowedFor mode p m calls rank dst.frame.module dst.code := by
  induction move generalizing rank with
  | pure move => exact pure_allowed move ready
  | @context bytes bytes' f f' before after move saved tail ih =>
    obtain ⟨leading, suffix⟩ := (append_allowed (l := values saved ++ before) (r := tail)).mp ready
    have middle := ((append_allowed (l := values saved) (r := before)).mp leading).2
    have next := ih middle
    rw [← edge_module move] at suffix
    exact append_allowed.mpr ⟨append_allowed.mpr ⟨values_allowed saved, next⟩, suffix⟩
  | label move n ih =>
    have guard := single_allowed.mp ready
    cases guard with
    | label scalar inside => exact single_allowed.mpr (.label scalar (ih inside))
  | @underLoop bytes bytes' f f' before after result body move ih =>
    cases (single_allowed.mp ready) with
    | loopLabel restart inside =>
      have same : f'.module = f.module := edge_module move
      exact single_allowed.mpr (.loopLabel (same.symm ▸ restart) (ih inside))
  | frame move n outer ih =>
    have guard := single_allowed.mp ready
    cases guard with
    | frame found permitted scope arity inside =>
      exact single_allowed.mpr (.frame found permitted ((edge_module move).trans scope) arity (ih inside))
    | enteredFrame scalar permitted inside =>
      exact single_allowed.mpr (.enteredFrame scalar permitted (ih inside))
  | get _ => exact single_allowed.mpr (value_allowed _)
  | set _ => exact values_allowed []
  | resolve resolved =>
    have guard := source_allowed (single_allowed.mp ready)
    cases guard with
    | call linked found permitted =>
      cases Option.some.inj (linked.symm.trans resolved)
      exact single_allowed.mpr (.invoke found permitted)
  | @indirect bytes frame index selector fixed outcome selected slot resolved =>
    cases outcome with
    | resolved address =>
      have guard := source_allowed (ready _ (List.Mem.tail _ (List.Mem.head _)))
      cases guard with
      | callIndirect admitted =>
        obtain ⟨fn, found, _, permitted⟩ := p.indirect_target admitted selected resolved
        exact single_allowed.mpr (.invoke found permitted)
    | bounds | null | mismatch => exact single_allowed.mpr .trap
  | @enter bytes f a fn args found count =>
    have guard := single_allowed.mp (append_allowed.mp ready).2
    cases guard with
    | invoke matchesTarget permitted =>
      cases Option.some.inj (found.symm.trans matchesTarget)
      exact single_allowed.mpr (.frame found permitted rfl rfl (single_allowed.mpr
        (.label (p.function_checked checked found).1 (body_allowed checked found))))
  | load slot rule =>
    cases MemoryQuery.invert_at rule with
    | load => exact single_allowed.mpr (.source (.intConst ..))
    | loadTrap => exact single_allowed.mpr .trap
  | store _ _ => exact values_allowed []
  | storeTrap _ _ => exact single_allowed.mpr .trap
  | size _ _ | grow _ _ _ | growFail _ _ => exact values_allowed _

private theorem root_permitted (calls : CallMode) (rank : Nat) : calls.permits (rank + 1) rank := by
  cases calls with
  | ranked => exact Nat.lt_succ_self _
  | recursive => trivial

theorem initial_invoke {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {addr : FuncAddr}
    {fn : Function} {caller : Frame} (found : p.lookup addr = some fn) (args : List Value)
    {bytes : ByteArray} {minimum : Nat} (extent : mode.extent minimum bytes) :
    ReadyFor mode p m calls (fn.rank + 1) minimum ⟨bytes, caller, values args ++ [.invoke addr]⟩ :=
  ⟨extent, append_allowed.mpr ⟨values_allowed args,
    single_allowed.mpr (.invoke found (root_permitted calls fn.rank))⟩⟩

theorem initial_call {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray)
    (extent : mode.extent bytes.size bytes) :
    ReadyFor mode p m calls (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  ⟨extent, append_allowed.mpr ⟨values_allowed args,
    single_allowed.mpr (.source (.call resolved found (root_permitted calls fn.rank)))⟩⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs
