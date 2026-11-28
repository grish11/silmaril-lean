module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Proofs

open Execution.Runtime (FuncAddr MemAddr ModuleInst Value)
open CallResolution.Indirect (Outcome resolveTable)
open Computed

theorem split_i32 {stack : List Value} {resume : List NumType → Bool}
    (checked : Graph.checkCondition (Prefix.stackTypes stack) resume = true) :
    ∃ (saved : List Value) (bits : BitVec 32),
      stack = saved ++ [Value.int .i32 bits] ∧ resume (Prefix.stackTypes saved) = true := by
  cases stack using List.reverseRecOn with
  | nil => simp [Prefix.stackTypes, Graph.checkCondition] at checked
  | append_singleton saved v =>
    rcases v with ⟨type, bits⟩
    simp only [Prefix.stackTypes, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at checked
    cases type with
    | float kind => simp [Graph.checkCondition] at checked
    | int kind =>
      cases kind with
      | i32 => exact ⟨saved, bits, rfl, checked⟩
      | i64 => simp [Graph.checkCondition] at checked

theorem load_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.load offset :: rest) labels = true) :
    ∃ (saved : List Value) (address : BitVec 32),
      stack = saved ++ [Value.int .i32 address] ∧
      ∀ bits : BitVec 32, fn.checkRegion (Prefix.stackTypes (saved ++ [Value.int .i32 bits])) fallthrough rest labels = true := by
  change Graph.checkCondition (Prefix.stackTypes stack)
    (fun saved => fn.checkRegion (.int .i32 :: saved) fallthrough rest labels) = true at checked
  obtain ⟨saved, address, rfl, resume⟩ := split_i32 checked
  refine ⟨saved, address, rfl, fun bits => ?_⟩
  simpa [Prefix.stackTypes, Value.int, List.reverse_append] using resume

theorem grow_typed {fn : Function} {stack : List Value} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.grow :: rest) labels = true) :
    ∃ (saved : List Value) (delta : BitVec 32),
      stack = saved ++ [Value.int .i32 delta] ∧
      ∀ result : BitVec 32, fn.checkRegion (Prefix.stackTypes (saved ++ [Value.int .i32 result])) fallthrough rest labels = true :=
  load_typed (offset := 0) checked

theorem size_typed {fn : Function} {stack : List Value} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.size :: rest) labels = true) (pages : BitVec 32) :
    fn.checkRegion (Prefix.stackTypes (stack ++ [Value.int .i32 pages])) fallthrough rest labels = true := by
  change fn.checkRegion (.int .i32 :: Prefix.stackTypes stack) fallthrough rest labels = true at checked
  simpa [Prefix.stackTypes, List.reverse_append, Value.int] using checked

theorem indirect_typed {fn : Function} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.callIndirect index signature :: rest) labels = true) :
    ∃ (operands : List Value) (selector : BitVec 32), stack = operands ++ [Value.int .i32 selector] ∧
      Graph.SuffixTyped signature.params operands ∧
      fn.checkRegion (signature.results.reverse ++ (Prefix.stackTypes operands).drop signature.params.length)
        fallthrough rest labels = true := by
  change Graph.checkCondition (Prefix.stackTypes stack) (fun operands =>
    decide (operands.take signature.params.length = signature.params.reverse) &&
    fn.checkRegion (signature.results.reverse ++ operands.drop signature.params.length)
      fallthrough rest labels) = true at checked
  obtain ⟨operands, selector, rfl, checks⟩ := split_i32 checked
  obtain ⟨typed, resume⟩ := Bool.and_eq_true_iff.mp checks
  have shape : (Prefix.stackTypes operands).take signature.params.length = signature.params.reverse :=
    of_decide_eq_true typed
  exact ⟨operands, selector, rfl, shape, resume⟩

theorem store_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.store offset :: rest) labels = true) :
    ∃ (saved : List Value) (address word : BitVec 32),
      stack = saved ++ [Value.int .i32 address, Value.int .i32 word] ∧ fn.checkRegion (Prefix.stackTypes saved) fallthrough rest labels = true := by
  change Graph.checkCondition (Prefix.stackTypes stack)
    (fun args => Graph.checkCondition args (fun saved => fn.checkRegion saved fallthrough rest labels)) = true at checked
  obtain ⟨args, word, rfl, remaining⟩ := split_i32 checked
  obtain ⟨saved, address, rfl, tail⟩ := split_i32 remaining
  exact ⟨saved, address, word, by simp [List.append_assoc], tail⟩

theorem block_typed {fn : Function} {saved : List Value} {result : Option NumType}
    {body rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes saved) fallthrough (.block result body :: rest) labels = true) :
    fn.checkRegion [] result.toList body (result.toList :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true := by
  change (fn.checkRegion [] result.toList body (result.toList :: labels) &&
    fn.checkRegion (result.toList.reverse ++ Prefix.stackTypes saved) fallthrough rest labels) = true at checked
  obtain ⟨checkBody, checkTail⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨checkBody, fun delivered typed => ?_⟩
  simpa [Prefix.stackTypes, List.reverse_append, typed] using checkTail

theorem loop_typed {fn : Function} {saved : List Value} {result : Option NumType}
    {body rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes saved) fallthrough (.loop result body :: rest) labels = true) :
    fn.checkRegion [] result.toList body ([] :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true := by
  change (fn.checkRegion [] result.toList body ([] :: labels) &&
    fn.checkRegion (result.toList.reverse ++ Prefix.stackTypes saved) fallthrough rest labels) = true at checked
  obtain ⟨checkBody, checkTail⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨checkBody, fun delivered typed => ?_⟩
  simpa [Prefix.stackTypes, List.reverse_append, typed] using checkTail

theorem if_typed {fn : Function} {stack : List Value} {result : Option NumType}
    {left right rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.if_ result left right :: rest) labels = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] ∧
      fn.checkRegion [] result.toList left (result.toList :: labels) = true ∧ fn.checkRegion [] result.toList right (result.toList :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true := by
  change Graph.checkCondition (Prefix.stackTypes stack) (fun saved =>
    fn.checkRegion [] result.toList left (result.toList :: labels) && fn.checkRegion [] result.toList right (result.toList :: labels) &&
    fn.checkRegion (result.toList.reverse ++ saved) fallthrough rest labels) = true at checked
  obtain ⟨saved, condition, rfl, checks⟩ := split_i32 checked
  obtain ⟨arms, checkTail⟩ := Bool.and_eq_true_iff.mp checks
  obtain ⟨checkLeft, checkRight⟩ := Bool.and_eq_true_iff.mp arms
  refine ⟨saved, condition, rfl, checkLeft, checkRight, fun delivered typed => ?_⟩
  simpa [Prefix.stackTypes, List.reverse_append, typed] using checkTail

theorem branch_typed {fn : Function} {stack : List Value} {depth : LabelIdx} {result fallthrough : List NumType}
    {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.ranked (.br depth result) :: rest) labels = true) :
    labels[depth.toNat]? = some result ∧ Graph.SuffixTyped result stack := by
  change Graph.checkBranch labels (Prefix.stackTypes stack) depth result = true at checked
  unfold Graph.SuffixTyped
  exact of_decide_eq_true checked

theorem br_if_typed {fn : Function} {stack : List Value} {depth : LabelIdx} {result fallthrough : List NumType}
    {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.ranked (.brIf depth result) :: rest) labels = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] ∧
      labels[depth.toNat]? = some result ∧ Graph.SuffixTyped result saved ∧
      fn.checkRegion (Prefix.stackTypes saved) fallthrough rest labels = true := by
  change Graph.checkCondition (Prefix.stackTypes stack) (fun saved =>
    Graph.checkBranch labels saved depth result && fn.checkRegion saved fallthrough rest labels) = true at checked
  obtain ⟨saved, condition, rfl, checks⟩ := split_i32 checked
  obtain ⟨branch, tail⟩ := Bool.and_eq_true_iff.mp checks
  obtain ⟨target, payload⟩ := of_decide_eq_true branch
  exact ⟨saved, condition, rfl, target, payload, tail⟩

theorem br_table_typed {fn : Function} {stack : List Value} {depths : List LabelIdx} {fallback : LabelIdx}
    {result fallthrough : List NumType} {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough
      (.ranked (.brTable depths fallback result) :: rest) labels = true) :
    ∃ (saved : List Value) (selector : BitVec 32), stack = saved ++ [Value.int .i32 selector] ∧
      Graph.SuffixTyped result saved ∧ ∀ depth ∈ fallback :: depths, labels[depth.toNat]? = some result := by
  change Graph.checkCondition (Prefix.stackTypes stack) (fun saved =>
    Graph.checkBranch labels saved fallback result &&
      depths.all (fun depth => Graph.checkBranch labels saved depth result)) = true at checked
  obtain ⟨saved, selector, rfl, checks⟩ := split_i32 checked
  obtain ⟨fallbackOK, entriesOK⟩ := Bool.and_eq_true_iff.mp checks
  obtain ⟨target, payload⟩ := of_decide_eq_true fallbackOK
  refine ⟨saved, selector, rfl, payload, fun depth used => ?_⟩
  rcases List.mem_cons.mp used with rfl | used
  · exact target
  · exact (of_decide_eq_true (List.all_eq_true.mp entriesOK depth used)).1

theorem lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry := by
  unfold Table.lookup Program.table Program.lookup
  rw [List.getElem?_map]
  cases program.functions[address.value]? with
  | none => rfl
  | some slot => cases slot <;> rfl

private theorem lookup_mem {program : Program} {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) : some fn ∈ program.functions := by
  unfold Program.lookup at found
  cases h : program.functions[address.value]? with
  | none => simp [h] at found
  | some slot =>
    have eq : slot = some fn := by simpa [h] using found
    exact List.mem_of_getElem? (eq ▸ h)

theorem function_checked {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 ∧
      fn.code.all (fun op => fn.supports op mode (program.checkIndirect calls fn.rank fn.declaration.module)) = true ∧
      fn.WellTyped fn.initial fn.code ∧ fn.declaration.module.memories[0]? = some memory := by
  have each := (Bool.and_eq_true_iff.mp checked).2
  have body := List.all_eq_true.mp each (some fn) (lookup_mem found)
  simp only [Option.map_some, Option.getD_some, Function.checkV1, Bool.and_eq_true,
    decide_eq_true_eq, Function.WellTyped] at body ⊢
  exact ⟨body.1.1.1, body.1.1.2, body.1.2, body.2⟩

theorem linked_target {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧
      callee.declaration = target.declaration ∧ calls.permits fn.rank callee.rank := by
  have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1
  cases calls with
  | ranked =>
    have entry : program.table.lookup address = some fn.entry := by rw [lookup_table, found]; rfl
    have member := List.mem_of_getElem? (show program.table.entries[address.value]? = some (some fn.entry) by
      unfold Table.lookup at entry
      cases h : program.table.entries[address.value]? <;> simp_all)
    obtain ⟨callee, atTarget, resolves, declares, rank⟩ :=
      (Table.check_iff program.table).mp valid _ member target used
    rw [lookup_table] at atTarget
    obtain ⟨body, foundBody, rfl⟩ := Option.map_eq_some_iff.mp atTarget
    exact ⟨body, foundBody, resolves, declares, rank⟩
  | recursive =>
    unfold Program.checkLinks at valid
    have targets := List.all_eq_true.mp valid (some fn) (lookup_mem found)
    have link := List.all_eq_true.mp targets target used
    cases lookup : program.lookup target.address with
    | none => simp [lookup] at link
    | some callee =>
      have exactLink : callee.declaration = target.declaration ∧
          fn.declaration.module.funcs[target.index.toNat]? = some target.address := by
        simpa only [lookup, decide_eq_true_eq] using link
      exact ⟨callee, rfl, exactLink.2, exactLink.1, trivial⟩

theorem table_target {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true) {fixed : FixedTable}
    (selected : program.fixedTable = some fixed) {address : FuncAddr} (member : some address ∈ fixed.table.refs) :
    ∃ fn, program.lookup address = some fn := by
  have complete := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).2
  simp only [Program.checkTable, selected, Option.map_some, Option.getD_some] at complete
  have present := List.all_eq_true.mp complete (some address) member
  simpa only [Option.map_some, Option.getD_some, Option.isSome_iff_exists] using present

theorem indirect_link {program : Program} {calls : CallMode} {rank : Nat} {module : ModuleInst}
    {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (checked : program.checkIndirect calls rank module index signature = true) :
    ∃ fixed, program.fixedTable = some fixed ∧ module.tables[0]? = some fixed.address ∧
      module.types[index.toNat]? = some signature ∧ signature.results.length ≤ 1 ∧
      ∀ address fn, some address ∈ fixed.table.refs → program.lookup address = some fn →
        fn.declaration.type = signature → calls.permits rank fn.rank := by
  cases selected : program.fixedTable with
  | none => simp [Program.checkIndirect, selected] at checked
  | some fixed =>
    simp only [Program.checkIndirect, selected, Option.map_some, Option.getD_some, Bool.and_eq_true_iff,
      decide_eq_true_eq] at checked
    refine ⟨fixed, rfl, checked.1.1, checked.1.2.1, checked.1.2.2, ?_⟩
    intro address fn member found
    have permits := List.all_eq_true.mp checked.2 (some address) member
    simpa only [Option.map_some, Option.getD_some, found, decide_eq_true_eq] using permits

theorem indirect_target {program : Program} {calls : CallMode} {rank : Nat} {module : ModuleInst}
    {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (checked : program.checkIndirect calls rank module index signature = true)
    {fixed : FixedTable} (selected : program.fixedTable = some fixed) {selector : BitVec 32} {address : FuncAddr}
    (resolved : program.resolveIndirect fixed module index selector = some (.resolved address)) :
    ∃ fn, program.lookup address = some fn ∧ fn.declaration.type = signature ∧ calls.permits rank fn.rank := by
  obtain ⟨table, h, _, expected, _, guard⟩ := indirect_link checked
  cases Option.some.inj (selected.symm.trans h)
  cases entry : fixed.table.refs[selector.toNat]? with
  | none => simp [Program.resolveIndirect, resolveTable, entry] at resolved
  | some elem =>
    cases elem with
    | none => simp [Program.resolveIndirect, resolveTable, entry] at resolved
    | some target =>
      cases found : program.lookup target with
      | none => simp [Program.resolveIndirect, resolveTable, entry, expected, found] at resolved
      | some fn =>
        by_cases same : fn.declaration.type = signature
        · simp [Program.resolveIndirect, resolveTable, entry, expected, found, same] at resolved
          subst target
          exact ⟨fn, found, same, guard address fn (List.mem_of_getElem? entry) found same⟩
        · simp [Program.resolveIndirect, resolveTable, entry, expected, found, same] at resolved

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Proofs
