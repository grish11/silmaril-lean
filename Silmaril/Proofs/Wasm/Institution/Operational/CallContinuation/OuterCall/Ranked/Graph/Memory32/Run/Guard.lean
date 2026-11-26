module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame FuncAddr MemAddr ModuleInst Value)
open Wasm.V1.Execution

theorem append_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {l r : List Admin} :
    CodeAllowed p m rank mod (l ++ r) ↔ CodeAllowed p m rank mod l ∧ CodeAllowed p m rank mod r := by
  simp only [CodeAllowed, List.mem_append, or_imp, forall_and]

theorem single_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {x : Admin} :
    CodeAllowed p m rank mod [x] ↔ Allowed p m rank mod x := by
  simp [CodeAllowed]

theorem value_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (v : Value) :
    Allowed p m rank mod (value v) := by
  rcases v with ⟨t, bits⟩
  cases t with
  | int width => exact .source (.intConst width bits)
  | float width => exact .source (.floatConst width bits)

theorem values_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (vs : List Value) :
    CodeAllowed p m rank mod (values vs) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact value_allowed v

theorem source_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {i : Wasm.V1.Instr}
    (guard : Allowed p m rank mod (.source i)) : SourceAllowed p m rank mod i := by
  cases guard with | source h => exact h

mutual

private theorem code_sources {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {a : FuncAddr} {fn : Function} (found : p.lookup a = some fn)
    (slot : fn.declaration.module.memories[0]? = some m) (code : List Op)
    (labels : List (List NumType)) (supported : supportedCode code labels = true)
    (targets : ∀ target ∈ codeTargets code, target ∈ fn.targets) :
    ∀ i ∈ v1Code code, SourceAllowed p m fn.rank fn.declaration.module i := by
  cases code with
  | nil => simp [v1Code]
  | cons op rest =>
    have checks := Bool.and_eq_true_iff.mp supported
    intro i hi
    simp only [v1Code, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact op_source checked found slot op labels checks.1
        (fun target used => targets target (List.mem_append_left _ used))
    · exact code_sources checked found slot rest labels checks.2
        (fun target used => targets target (List.mem_append_right _ used)) i hi

private theorem op_source {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {a : FuncAddr} {fn : Function} (found : p.lookup a = some fn)
    (slot : fn.declaration.module.memories[0]? = some m) (op : Op)
    (labels : List (List NumType)) (supported : op.supportedIn labels = true)
    (targets : ∀ target ∈ op.targets, target ∈ fn.targets) :
    SourceAllowed p m fn.rank fn.declaration.module op.v1 := by
  cases op with
  | load offset => exact .load offset slot
  | store offset => exact .store offset slot
  | block result body =>
    exact .block (code_sources checked found slot body (result.toList :: labels) supported targets)
  | loop result body =>
    exact .loop (code_sources checked found slot body ([] :: labels) supported targets)
  | if_ result left right =>
    have checks := Bool.and_eq_true_iff.mp supported
    exact .if_
      (code_sources checked found slot left (result.toList :: labels) checks.1
        (fun target used => targets target (List.mem_append_left _ used)))
      (code_sources checked found slot right (result.toList :: labels) checks.2
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
      obtain ⟨callee, h, resolved, _, smaller⟩ := p.linked_target checked found uses
      exact .call resolved h smaller
    | _ => contradiction

end

theorem body_allowed {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {a : FuncAddr} {fn : Function} (found : p.lookup a = some fn) :
    CodeAllowed p m fn.rank fn.declaration.module (expression fn.v1Func.body) := by
  obtain ⟨_, supported, _, slot⟩ := p.function_checked checked found
  rw [fn.body_expression, append_allowed]
  refine ⟨values_allowed _, ?_⟩
  intro x member
  obtain ⟨op, used, rfl⟩ := List.mem_map.mp member
  exact .source (op_source checked found slot op fn.entryLabels (List.all_eq_true.mp supported op used)
    (fun target h => List.mem_flatMap.mpr ⟨op, used, h⟩))

private theorem expression_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {code : Wasm.V1.Expr} (guard : ∀ i ∈ code, SourceAllowed p m rank mod i) :
    CodeAllowed p m rank mod (expression code) := by
  intro x member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  exact .source (guard i hi)

theorem pure_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {before after : List Admin} (move : PureStep before after)
    (guard : CodeAllowed p m rank mod before) : CodeAllowed p m rank mod after := by
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
    change CodeAllowed p m rank mod (values [v, v] ++ [.source (.localSet i)])
    exact append_allowed.mpr ⟨values_allowed _, single_allowed.mpr (.source (.set i))⟩
  | _ =>
    first
    | exact values_allowed _
    | exact values_allowed []
    | exact single_allowed.mpr (value_allowed _)
    | exact single_allowed.mpr .trap

theorem edge_module {p : Program} {m : MemAddr} {src dst : State} (move : Edge p m src dst) :
    dst.frame.module = src.frame.module := by
  induction move <;> first | rfl | assumption

theorem edge_extent {p : Program} {m : MemAddr} {src dst : State} (move : Edge p m src dst) :
    dst.bytes.size = src.bytes.size := by
  induction move <;> first | rfl | assumption | exact MemoryWrite.closed_at ‹_›

theorem preserve {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {src dst : State} (move : Edge p m src dst) {rank : Nat}
    (ready : CodeAllowed p m rank src.frame.module src.code) :
    CodeAllowed p m rank dst.frame.module dst.code := by
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
    | frame found smaller scope arity inside =>
      exact single_allowed.mpr (.frame found smaller ((edge_module move).trans scope) arity (ih inside))
  | get _ => exact single_allowed.mpr (value_allowed _)
  | set _ => exact values_allowed []
  | resolve resolved =>
    have guard := source_allowed (single_allowed.mp ready)
    cases guard with
    | call linked found smaller =>
      cases Option.some.inj (linked.symm.trans resolved)
      exact single_allowed.mpr (.invoke found smaller)
  | @enter bytes f a fn args found count =>
    have guard := single_allowed.mp (append_allowed.mp ready).2
    cases guard with
    | invoke matchesTarget smaller =>
      cases Option.some.inj (found.symm.trans matchesTarget)
      exact single_allowed.mpr (.frame found smaller rfl rfl (single_allowed.mpr
        (.label (p.function_checked checked found).1 (body_allowed checked found))))
  | load slot rule =>
    cases MemoryQuery.invert_at rule with
    | load => exact single_allowed.mpr (.source (.intConst ..))
    | loadTrap => exact single_allowed.mpr .trap
  | store _ _ => exact values_allowed []
  | storeTrap _ _ => exact single_allowed.mpr .trap

theorem initial_call {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray) :
    Ready p m (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  ⟨rfl, append_allowed.mpr ⟨values_allowed args,
    single_allowed.mpr (.source (.call resolved found (Nat.lt_succ_self _)))⟩⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs
