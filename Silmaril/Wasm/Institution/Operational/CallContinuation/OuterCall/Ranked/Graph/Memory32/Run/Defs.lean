module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs

/-!
# Finite checked V1 Memory32 execution

Administrative code retains the native operand, label and frame structure.
The machine carries the selected memory's bytes once, outside that structure.
Its non-memory pure moves reuse V1's store-independent reduction.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution

/-- A suspended frame contains its native locals, code and continuation.
The bytes belong to the state shared by every frame. -/
structure State where
  bytes : ByteArray
  frame : Frame
  code : List Admin

/-- Source instructions admitted in the current module and call profile. Branch
payload types are checked at source entry. This administrative guard admits
native depth lowering under entered labels. -/
inductive SourceAllowedFor (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode) (rank : Nat) (module : ModuleInst) :
    Wasm.V1.Instr → Prop where
  | intConst (t : IntType) (bits : BitVec t.width) : SourceAllowedFor mode program memory calls rank module (.intConst t bits)
  | floatConst (t : FloatType) (bits : BitVec t.width) : SourceAllowedFor mode program memory calls rank module (.floatConst t bits)
  | get (i : LocalIdx) : SourceAllowedFor mode program memory calls rank module (.localGet i)
  | set (i : LocalIdx) : SourceAllowedFor mode program memory calls rank module (.localSet i)
  | tee (i : LocalIdx) : SourceAllowedFor mode program memory calls rank module (.localTee i)
  | bin (t : IntType) (op : IntBinOp) : SourceAllowedFor mode program memory calls rank module (.intBinOp t op)
  | call {i : FuncIdx} {a : FuncAddr} {fn : Function}
      (resolved : module.funcs[i.toNat]? = some a) (found : program.lookup a = some fn)
      (permitted : calls.permits rank fn.rank) : SourceAllowedFor mode program memory calls rank module (.call i)
  | load (offset : Fin (2 ^ 32)) (slot : module.memories[0]? = some memory) :
      SourceAllowedFor mode program memory calls rank module (.intLoad .i32 none (immediate offset))
  | store (offset : Fin (2 ^ 32)) (slot : module.memories[0]? = some memory) :
      SourceAllowedFor mode program memory calls rank module (.intStore .i32 none (immediate offset))
  | memorySize {maximum : Option Nat} (enabled : mode = .growing maximum)
      (slot : module.memories[0]? = some memory) :
      SourceAllowedFor mode program memory calls rank module .memorySize
  | memoryGrow {maximum : Option Nat} (enabled : mode = .growing maximum)
      (slot : module.memories[0]? = some memory) :
      SourceAllowedFor mode program memory calls rank module .memoryGrow
  | if_ {result : Option NumType} {left right : Wasm.V1.Expr}
      (thenBody : ∀ i ∈ left, SourceAllowedFor mode program memory calls rank module i)
      (elseBody : ∀ i ∈ right, SourceAllowedFor mode program memory calls rank module i) :
      SourceAllowedFor mode program memory calls rank module (.if_ result left right)
  -- Source blocks and selected conditional arms open the same kind of native label.
  | block {result : Option NumType} {body : Wasm.V1.Expr}
      (guard : ∀ i ∈ body, SourceAllowedFor mode program memory calls rank module i) :
      SourceAllowedFor mode program memory calls rank module (.block result body)
  | loop {result : Option NumType} {body : Wasm.V1.Expr}
      (guard : ∀ i ∈ body, SourceAllowedFor mode program memory calls rank module i) :
      SourceAllowedFor mode program memory calls rank module (.loop result body)
  | br (depth : LabelIdx) : SourceAllowedFor mode program memory calls rank module (.br depth)
  | brIf (depth : LabelIdx) : SourceAllowedFor mode program memory calls rank module (.brIf depth)
  | brTable (depths : List LabelIdx) (fallback : LabelIdx) :
      SourceAllowedFor mode program memory calls rank module (.brTable depths fallback)
  | unreachable : SourceAllowedFor mode program memory calls rank module .unreachable
  | return_ : SourceAllowedFor mode program memory calls rank module .return_

/-- The active module and, in the ranked profile, the rank ceiling are local
to a frame. The recursive case is still inductive on finite administrative code. -/
inductive AllowedFor (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode) : Nat → ModuleInst → Admin → Prop where
  | source {rank module i} (guard : SourceAllowedFor mode program memory calls rank module i) :
      AllowedFor mode program memory calls rank module (.source i)
  | trap {rank module} : AllowedFor mode program memory calls rank module .trap
  | invoke {rank module address fn} (found : program.lookup address = some fn)
      (permitted : calls.permits rank fn.rank) : AllowedFor mode program memory calls rank module (.invoke address)
  | label {rank module n body} (scalar : n ≤ 1) (inside : ∀ x ∈ body, AllowedFor mode program memory calls rank module x) :
      AllowedFor mode program memory calls rank module (.label n [] body)
  | loopLabel {rank module result loopBody body}
      (restart : SourceAllowedFor mode program memory calls rank module (.loop result loopBody))
      (inside : ∀ x ∈ body, AllowedFor mode program memory calls rank module x) :
      AllowedFor mode program memory calls rank module (.label 0 [.loop result loopBody] body)
  | frame {rank module n callee body address fn} (found : program.lookup address = some fn)
      (permitted : calls.permits rank fn.rank) (scope : callee.module = fn.declaration.module)
      (arity : n = fn.declaration.results.length)
      (inside : ∀ x ∈ body, AllowedFor mode program memory calls fn.rank callee.module x) :
      AllowedFor mode program memory calls rank module (.frame n callee body)

abbrev CodeAllowedFor (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode) (rank : Nat) (module : ModuleInst)
    (code : List Admin) : Prop :=
  ∀ x ∈ code, AllowedFor mode program memory calls rank module x

def ReadyFor (mode : MemoryMode) (program : Program) (memory : MemAddr) (calls : CallMode) (rank : Nat) (extent : Nat) (state : State) : Prop :=
  mode.extent extent state.bytes ∧ CodeAllowedFor mode program memory calls rank state.frame.module state.code

/-- One native administrative operation at a time. The frame and context
congruences thread the same bytes into and out of their premises. -/
inductive EdgeAt (mode : MemoryMode) (program : Program) (memory : MemAddr) : State → State → Prop where
  | pure {bytes f before after} (move : PureStep before after) :
      EdgeAt mode program memory ⟨bytes, f, before⟩ ⟨bytes, f, after⟩
  | context {bytes bytes' f f' before after}
      (move : EdgeAt mode program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩)
      (saved : List Value) (tail : List Admin) :
      EdgeAt mode program memory ⟨bytes, f, values saved ++ before ++ tail⟩
        ⟨bytes', f', values saved ++ after ++ tail⟩
  | label {bytes bytes' f f' before after}
      (move : EdgeAt mode program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩) (n : Nat) :
      EdgeAt mode program memory ⟨bytes, f, [.label n [] before]⟩ ⟨bytes', f', [.label n [] after]⟩
  | underLoop {bytes bytes' f f' before after} (result : Option NumType) (body : Wasm.V1.Expr)
      (move : EdgeAt mode program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩) :
      EdgeAt mode program memory ⟨bytes, f, [.label 0 [.loop result body] before]⟩
        ⟨bytes', f', [.label 0 [.loop result body] after]⟩
  | frame {bytes bytes' inner inner' before after}
      (move : EdgeAt mode program memory ⟨bytes, inner, before⟩ ⟨bytes', inner', after⟩)
      (n : Nat) (outer : Frame) :
      EdgeAt mode program memory ⟨bytes, outer, [.frame n inner before]⟩
        ⟨bytes', outer, [.frame n inner' after]⟩
  | get {bytes f i v} (found : f.locals[i.toNat]? = some v) :
      EdgeAt mode program memory ⟨bytes, f, [.source (.localGet i)]⟩ ⟨bytes, f, [value v]⟩
  | set {bytes f i v old} (found : f.locals[i.toNat]? = some old) :
      EdgeAt mode program memory ⟨bytes, f, [value v, .source (.localSet i)]⟩
        ⟨bytes, { f with locals := f.locals.set i.toNat v }, []⟩
  | resolve {bytes f i address} (found : f.module.funcs[i.toNat]? = some address) :
      EdgeAt mode program memory ⟨bytes, f, [.source (.call i)]⟩ ⟨bytes, f, [.invoke address]⟩
  | enter {bytes f address fn args} (found : program.lookup address = some fn)
      (count : args.length = fn.declaration.params.length) :
      EdgeAt mode program memory ⟨bytes, f, values args ++ [.invoke address]⟩
        ⟨bytes, f, [.frame fn.declaration.results.length (fn.declaration.frame args)
          [.label fn.declaration.results.length [] (expression fn.v1Func.body)]]⟩
  | load {bytes f arg address out} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryQuery.EdgeAt bytes arg.offset.val (.load address) out) :
      EdgeAt mode program memory ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load address)⟩
        ⟨bytes, f, MemoryQuery.v1CodeAt arg out⟩
  | store {bytes f arg address word written} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryWrite.EdgeAt bytes arg.offset.val (.store address word) (.written written)) :
      EdgeAt mode program memory ⟨bytes, f, [value (.int .i32 address), value (.int .i32 word),
        .source (.intStore .i32 none arg)]⟩ ⟨written, f, []⟩
  | storeTrap {bytes f arg address word} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryWrite.EdgeAt bytes arg.offset.val (.store address word) .trap) :
      EdgeAt mode program memory ⟨bytes, f, [value (.int .i32 address), value (.int .i32 word),
        .source (.intStore .i32 none arg)]⟩ ⟨bytes, f, [.trap]⟩

  | size {bytes f maximum} (enabled : mode = .growing maximum) (slot : f.module.memories[0]? = some memory) :
      EdgeAt mode program memory ⟨bytes, f, [.source .memorySize]⟩
        ⟨bytes, f, values [Value.int .i32 (BitVec.ofNat 32 (Execution.Memory.size bytes))]⟩
  | grow {bytes f maximum delta grown} (enabled : mode = .growing maximum)
      (slot : f.module.memories[0]? = some memory)
      (rule : MemoryGrow.Edge ⟨bytes, maximum⟩ (.request delta) (.grown grown)) :
      EdgeAt mode program memory ⟨bytes, f, [value (.int .i32 delta), .source .memoryGrow]⟩
        ⟨grown, f, values [Value.int .i32 (BitVec.ofNat 32 (Execution.Memory.size bytes))]⟩
  | growFail {bytes f maximum delta} (enabled : mode = .growing maximum)
      (slot : f.module.memories[0]? = some memory) :
      EdgeAt mode program memory ⟨bytes, f, [value (.int .i32 delta), .source .memoryGrow]⟩
        ⟨bytes, f, values [Value.int .i32 (-1)]⟩

abbrev RunsAt (mode : MemoryMode) (program : Program) (memory : MemAddr) :=
  Relation.ReflTransGen (EdgeAt mode program memory)

abbrev SourceAllowedAt mode program memory := SourceAllowedFor mode program memory .ranked
abbrev AllowedAt mode program memory := AllowedFor mode program memory .ranked
abbrev CodeAllowedAt mode program memory := CodeAllowedFor mode program memory .ranked
abbrev ReadyAt mode program memory := ReadyFor mode program memory .ranked

abbrev SourceAllowed := SourceAllowedAt .fixed
abbrev Allowed := AllowedAt .fixed
abbrev CodeAllowed := CodeAllowedAt .fixed
abbrev Ready := ReadyAt .fixed
abbrev Edge := EdgeAt .fixed
abbrev Runs := RunsAt .fixed

def render {H : Type} (base : Store H) (memory : MemAddr) (initial : MemInst) (state : State) :
    Config H :=
  ⟨storeWithBytes base memory initial state.bytes, state.frame, state.code⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
