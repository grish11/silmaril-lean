module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Typing
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Store

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution
open Computed

/-- A checked i32 test exposes the ordered operands used by its continuation. -/
theorem split_i32 {stack : List Value} {resume : List NumType → Bool}
    (checked : Graph.checkCondition (Prefix.stackTypes stack) resume = true) :
    ∃ (saved : List Value) (bits : BitVec 32),
      stack = saved ++ [Value.int .i32 bits] ∧ resume (Prefix.stackTypes saved) = true :=
  Proofs.split_i32 checked

/-- The selector is above the ordered argument suffix. The continuation
receives the declared results above the saved operand types. -/
theorem Function.indirect_typed {fn : Function} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.callIndirect index signature :: rest) labels = true) :
    ∃ (operands : List Value) (selector : BitVec 32), stack = operands ++ [Value.int .i32 selector] ∧
      Graph.SuffixTyped signature.params operands ∧
      fn.checkRegion (signature.results.reverse ++ (Prefix.stackTypes operands).drop signature.params.length)
        fallthrough rest labels = true :=
  Proofs.indirect_typed checked

/-- An admitted load has an i32 address and preserves the continuation's stack types. -/
theorem Function.load_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    (checked : fn.WellTyped stack (.load offset :: rest)) :
    ∃ (saved : List Value) (address : BitVec 32),
      stack = saved ++ [Value.int .i32 address] ∧
      ∀ bits : BitVec 32, fn.WellTyped (saved ++ [Value.int .i32 bits]) rest :=
  Proofs.load_typed checked

/-- Growth consumes an i32 delta and returns an i32 on both native outcomes. -/
theorem Function.grow_typed {fn : Function} {stack : List Value} {rest : List Op}
    (checked : fn.WellTyped stack (.grow :: rest)) :
    ∃ (saved : List Value) (delta : BitVec 32),
      stack = saved ++ [Value.int .i32 delta] ∧
      ∀ result : BitVec 32, fn.WellTyped (saved ++ [Value.int .i32 result]) rest :=
  Proofs.grow_typed checked

/-- Size appends an i32 page count above the saved operands. -/
theorem Function.size_typed {fn : Function} {stack : List Value} {rest : List Op}
    (checked : fn.WellTyped stack (.size :: rest)) (pages : BitVec 32) :
    fn.WellTyped (stack ++ [Value.int .i32 pages]) rest :=
  Proofs.size_typed checked pages

/-- An admitted store consumes the address and then the word in operand delivery order. -/
theorem Function.store_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    (checked : fn.WellTyped stack (.store offset :: rest)) :
    ∃ (saved : List Value) (address word : BitVec 32),
      stack = saved ++ [Value.int .i32 address, Value.int .i32 word] ∧ fn.WellTyped saved rest :=
  Proofs.store_typed checked

theorem Function.region_load_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.load offset :: rest) labels = true) :
    ∃ (saved : List Value) (address : BitVec 32),
      stack = saved ++ [Value.int .i32 address] ∧
      ∀ bits : BitVec 32, fn.checkRegion (Prefix.stackTypes (saved ++ [Value.int .i32 bits])) fallthrough rest labels = true :=
  Proofs.load_typed checked

theorem Function.region_grow_typed {fn : Function} {stack : List Value} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.grow :: rest) labels = true) :
    ∃ (saved : List Value) (delta : BitVec 32),
      stack = saved ++ [Value.int .i32 delta] ∧
      ∀ result : BitVec 32, fn.checkRegion (Prefix.stackTypes (saved ++ [Value.int .i32 result])) fallthrough rest labels = true :=
  Proofs.grow_typed checked

theorem Function.region_size_typed {fn : Function} {stack : List Value} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.size :: rest) labels = true) (pages : BitVec 32) :
    fn.checkRegion (Prefix.stackTypes (stack ++ [Value.int .i32 pages])) fallthrough rest labels = true :=
  Proofs.size_typed checked pages

theorem Function.region_store_typed {fn : Function} {stack : List Value} {offset : Fin (2 ^ 32)} {rest : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.store offset :: rest) labels = true) :
    ∃ (saved : List Value) (address word : BitVec 32),
      stack = saved ++ [Value.int .i32 address, Value.int .i32 word] ∧ fn.checkRegion (Prefix.stackTypes saved) fallthrough rest labels = true :=
  Proofs.store_typed checked

/-- A parameterless block checks its body in isolation and delivers its optional result above the saved operands. -/
theorem Function.block_typed {fn : Function} {saved : List Value} {result : Option NumType}
    {body rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes saved) fallthrough (.block result body :: rest) labels = true) :
    fn.checkRegion [] result.toList body (result.toList :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true :=
  Proofs.block_typed checked

/-- The loop label takes no restart operands. Normal fallthrough delivers the declared result. -/
theorem Function.loop_typed {fn : Function} {saved : List Value} {result : Option NumType}
    {body rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes saved) fallthrough (.loop result body :: rest) labels = true) :
    fn.checkRegion [] result.toList body ([] :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true :=
  Proofs.loop_typed checked

/-- Both arms have the same declared fallthrough types. The continuation resumes above the saved prefix. -/
theorem Function.if_typed {fn : Function} {stack : List Value} {result : Option NumType}
    {left right rest : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.if_ result left right :: rest) labels = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] ∧
      fn.checkRegion [] result.toList left (result.toList :: labels) = true ∧ fn.checkRegion [] result.toList right (result.toList :: labels) = true ∧
      ∀ delivered : List Value, delivered.map Value.type = result.toList →
        fn.checkRegion (Prefix.stackTypes (saved ++ delivered)) fallthrough rest labels = true :=
  Proofs.if_typed checked

/-- The immediate resolves in the active labels and the operand suffix matches. -/
theorem Function.branch_typed {fn : Function} {stack : List Value} {depth : LabelIdx}
    {result fallthrough : List NumType} {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.ranked (.br depth result) :: rest) labels = true) :
    labels[depth.toNat]? = some result ∧ Graph.SuffixTyped result stack :=
  Proofs.branch_typed checked

/-- A conditional branch validates its target even when zero, and the untaken path keeps the payload. -/
theorem Function.br_if_typed {fn : Function} {stack : List Value} {depth : LabelIdx}
    {result fallthrough : List NumType} {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough (.ranked (.brIf depth result) :: rest) labels = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] ∧
      labels[depth.toNat]? = some result ∧ Graph.SuffixTyped result saved ∧
      fn.checkRegion (Prefix.stackTypes saved) fallthrough rest labels = true :=
  Proofs.br_if_typed checked

/-- The selector is i32 and all listed depths and the default accept the same typed suffix. -/
theorem Function.br_table_typed {fn : Function} {stack : List Value} {depths : List LabelIdx} {fallback : LabelIdx}
    {result fallthrough : List NumType} {rest : List Op} {labels : List (List NumType)}
    (checked : fn.checkRegion (Prefix.stackTypes stack) fallthrough
      (.ranked (.brTable depths fallback result) :: rest) labels = true) :
    ∃ (saved : List Value) (selector : BitVec 32), stack = saved ++ [Value.int .i32 selector] ∧
      Graph.SuffixTyped result saved ∧ ∀ depth ∈ fallback :: depths, labels[depth.toNat]? = some result :=
  Proofs.br_table_typed checked

/-- The function label follows all explicitly enclosing source labels. -/
theorem Function.function_label_types (fn : Function) {labels : List (List NumType)} {result : List NumType}
    (target : (labels ++ fn.entryLabels)[labels.length]? = some result) :
    result = fn.declaration.results := by
  simpa [Function.entryLabels, List.getElem?_append_right] using target.symm

/-- The rank table is derived from the declared bodies. -/
theorem Program.lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry :=
  Proofs.lookup_table program address

/-- Recover the V1 arity, source, stack, and shared-memory slot checks. -/
theorem Program.function_checked {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 ∧
      fn.code.all (fun op => fn.supports op mode (program.checkIndirect calls fn.rank fn.declaration.module)) = true ∧
      fn.WellTyped fn.initial fn.code ∧ fn.declaration.module.memories[0]? = some memory :=
  Proofs.function_checked checked found

/-- Both profiles bind the direct index and the callee's declaration. The ranked
profile additionally requires a strictly smaller rank. -/
theorem Program.linked_target {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address ∧
      callee.declaration = target.declaration ∧ calls.permits fn.rank callee.rank :=
  Proofs.linked_target checked found used

/-- Every initialized entry in the fixed table names a graph declaration. -/
theorem Program.table_target {program : Program} {memory : MemAddr} {mode : MemoryMode} {calls : CallMode}
    (checked : program.checkV1 memory mode calls = true) {fixed : FixedTable}
    (selected : program.fixedTable = some fixed) {address : FuncAddr} (member : some address ∈ fixed.table.refs) :
    ∃ fn, program.lookup address = some fn :=
  Proofs.table_target checked selected member

/-- A checked site binds the active caller's table and type index. Rank
descent applies to entries that can pass the exact signature test. -/
theorem Program.indirect_link {program : Program} {calls : CallMode} {rank : Nat} {module : ModuleInst}
    {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (checked : program.checkIndirect calls rank module index signature = true) :
    ∃ fixed, program.fixedTable = some fixed ∧ module.tables[0]? = some fixed.address ∧
      module.types[index.toNat]? = some signature ∧ signature.results.length ≤ 1 ∧
      ∀ address fn, some address ∈ fixed.table.refs → program.lookup address = some fn →
        fn.declaration.type = signature → calls.permits rank fn.rank :=
  Proofs.indirect_link checked

theorem Program.indirect_target {program : Program} {calls : CallMode} {rank : Nat} {module : ModuleInst}
    {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (checked : program.checkIndirect calls rank module index signature = true)
    {fixed : FixedTable} (selected : program.fixedTable = some fixed) {selector : BitVec 32} {address : FuncAddr}
    (resolved : program.resolveIndirect fixed module index selector = some (.resolved address)) :
    ∃ fn, program.lookup address = some fn ∧ fn.declaration.type = signature ∧ calls.permits rank fn.rank :=
  Proofs.indirect_target checked selected resolved

/-- The base store starts at the original extent and allocation. -/
theorem Layout.initial_shared {H : Type} {program : Program} {base : Store H} {a : MemAddr} {initial : MemInst}
    (layout : Layout program base a initial) : SharedStore base a initial base :=
  Proofs.initial_shared layout

/-- Updating the live array preserves the selected allocation and all checked functions. -/
theorem Layout.with_bytes {H : Type} {program : Program} {base : Store H} {a : MemAddr} {initial : MemInst}
    (layout : Layout program base a initial) (bytes : ByteArray) :
    Layout program (storeWithBytes base a initial bytes) a { initial with data := bytes } :=
  Proofs.layout_with_bytes layout bytes

/-- Successful growth preserves the numeric bounds on the selected extent. -/
theorem BoundedExtent.grow {minimum : Nat} {maximum : Option Nat} {bytes grown : ByteArray} {delta : BitVec 32}
    (extent : BoundedExtent minimum maximum bytes)
    (edge : MemoryGrow.Edge ⟨bytes, maximum⟩ (.request delta) (.grown grown)) :
    BoundedExtent minimum maximum grown :=
  Proofs.bounded_extent_grow extent edge

/-- Successful growth preserves the aligned, bounded, nondecreasing extent. -/
theorem GrowthExtent.grow {initial : MemInst} {bytes grown : ByteArray} {delta : BitVec 32}
    (extent : GrowthExtent initial bytes)
    (edge : MemoryGrow.Edge { initial with data := bytes } (.request delta) (.grown grown)) :
    GrowthExtent initial grown :=
  Proofs.bounded_extent_grow extent edge

/-- A native growth result uses the same store representation at its new extent. -/
theorem GrowingStore.grow {H : Type} {base : Store H} {a : MemAddr} {initial : MemInst}
    {bytes grown : ByteArray} {delta : BitVec 32} (extent : GrowthExtent initial bytes)
    (edge : MemoryGrow.Edge { initial with data := bytes } (.request delta) (.grown grown)) :
    GrowingStore base a initial (setMemory (storeWithBytes base a initial bytes) a
      { initial with data := grown }) :=
  ⟨grown, extent.grow edge, by simp [storeWithBytes, setMemory, List.set_set]⟩

/-- Stores after growth preserve the live extent. -/
theorem GrowingStore.write {H : Type} {base : Store H} {a : MemAddr} {initial : MemInst}
    {bytes written : ByteArray} {offset : Nat} {address word : BitVec 32}
    (extent : GrowthExtent initial bytes)
    (edge : MemoryWrite.EdgeAt bytes offset (.store address word) (.written written)) :
    GrowingStore base a initial (setMemory (storeWithBytes base a initial bytes) a
      { initial with data := written }) :=
  Proofs.growth_write extent edge

/-- Any checked activation selects the same current memory at slot zero. -/
theorem Layout.frame_memory {H : Type} {program : Program} {base : Store H} {a : MemAddr} {initial : MemInst}
    {mode : MemoryMode} (checked : program.checkV1 a mode = true) (layout : Layout program base a initial)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (locals : List Value) (bytes : ByteArray) :
    frameMemory (storeWithBytes base a initial bytes) (Graph.currentFrame fn.declaration locals) =
      some (a, { initial with data := bytes }) :=
  Proofs.frame_memory checked layout found locals bytes

/-- A successful write preserves the fixed extent and composes with the preceding byte update. -/
theorem SharedStore.write {H : Type} {base : Store H} {a : MemAddr} {initial : MemInst}
    {bytes written : ByteArray} {offset : Nat} {address word : BitVec 32}
    (extent : bytes.size = initial.data.size)
    (edge : MemoryWrite.EdgeAt bytes offset (.store address word) (.written written)) :
    SharedStore base a initial (setMemory (storeWithBytes base a initial bytes) a
      { initial with data := written }) :=
  Proofs.update_shared extent edge

/-- Memory writes preserve exact native allocations for every declared function. -/
theorem Layout.function_allocated {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} (layout : Layout program base a initial)
    (shared : SharedStore base a initial live)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    live.funcs[address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func) :=
  Proofs.function_allocated layout shared found

/-- The allocated body renders the literal prefix followed by the checked instructions. -/
theorem Function.body_expression (fn : Function) :
    expression fn.v1Func.body = values fn.initial ++ fn.code.map (.source ∘ Op.v1) :=
  Proofs.body_expression fn

/-- Enter the allocated V1 function with the shared store intact and its scalar arity. -/
theorem Layout.enter {H : Type} {program : Program} {base live : Store H} {a : MemAddr} {initial : MemInst}
    {mode : MemoryMode} (checked : program.checkV1 a mode = true) (layout : Layout program base a initial)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (shared : SharedStore base a initial live) {caller : Frame} {saved args : List Value} {tail : List Admin}
    (typed : args.map Value.type = fn.declaration.params) :
    Step CallFrame.v1NoHost ⟨live, caller, values (saved ++ args) ++ .invoke address :: tail⟩
      ⟨live, caller, MemoryWrite.v1ActivationCode fn.declaration.results.head? (fn.declaration.frame args)
        saved tail (expression fn.v1Func.body)⟩ :=
  Proofs.enter checked layout found shared typed

/-- Exact native contextual readback preserves shared allocation and extent on write or trap. -/
theorem Layout.store_activation_shared {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} {mode : MemoryMode} (checked : program.checkV1 a mode = true)
    (layout : Layout program base a initial) {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) (shared : SharedStore base a initial live)
    {caller : Frame} {locals callerSaved saved : List Value} {callerTail tail : List Admin}
    {offset : Fin (2 ^ 32)} {ptr word : BitVec 32} {dst : Config H}
    (move : Step CallFrame.v1NoHost ⟨live, caller,
      MemoryWrite.v1ActivationCode fn.declaration.results.head? (Graph.currentFrame fn.declaration locals)
        callerSaved callerTail (values saved ++ [.source (.intConst .i32 ptr),
          .source (.intConst .i32 word), .source ((Op.store offset).v1)] ++ tail)⟩ dst) :
    SharedStore base a initial dst.store ∧ dst.frame = caller :=
  Proofs.store_activation_shared checked layout found shared move

/-- A native load or load trap under the activation preserves the entire current store. -/
theorem Layout.load_activation_store {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} {mode : MemoryMode} (checked : program.checkV1 a mode = true)
    (layout : Layout program base a initial) {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) (shared : SharedStore base a initial live)
    {caller : Frame} {locals callerSaved saved : List Value} {callerTail tail : List Admin}
    {offset : Fin (2 ^ 32)} {ptr : BitVec 32} {dst : Config H}
    (move : Step CallFrame.v1NoHost ⟨live, caller,
      MemoryWrite.v1ActivationCode fn.declaration.results.head? (Graph.currentFrame fn.declaration locals)
        callerSaved callerTail (values saved ++ [.source (.intConst .i32 ptr),
          .source ((Op.load offset).v1)] ++ tail)⟩ dst) :
    dst.store = live ∧ dst.frame = caller :=
  Proofs.load_activation_store checked layout found shared move

/-- A completed return or trap at the frame boundary leaves the shared store and caller frame intact. -/
theorem exit_store {H : Type} {s : Store H} {caller callee : Frame} {arity : Nat}
    {saved : List Value} {tail : List Admin} {result : Nested.Result} {dst : Config H}
    (move : Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ .frame arity callee (Nested.resultCode values .trap result) :: tail⟩ dst) :
    dst.store = s ∧ dst.frame = caller :=
  Proofs.exit_store move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
