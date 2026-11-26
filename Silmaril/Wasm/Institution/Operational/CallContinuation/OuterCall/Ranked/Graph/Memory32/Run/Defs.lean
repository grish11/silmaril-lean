module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs

/-!
# Finite ranked V1 Memory32 execution

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

/-- Source instructions admitted at a given module and rank ceiling. Branch
payload types are checked at source entry. This administrative guard admits
native depth lowering under entered labels. -/
inductive SourceAllowed (program : Program) (memory : MemAddr) (rank : Nat) (module : ModuleInst) :
    Wasm.V1.Instr → Prop where
  | intConst (t : IntType) (bits : BitVec t.width) : SourceAllowed program memory rank module (.intConst t bits)
  | floatConst (t : FloatType) (bits : BitVec t.width) : SourceAllowed program memory rank module (.floatConst t bits)
  | get (i : LocalIdx) : SourceAllowed program memory rank module (.localGet i)
  | set (i : LocalIdx) : SourceAllowed program memory rank module (.localSet i)
  | tee (i : LocalIdx) : SourceAllowed program memory rank module (.localTee i)
  | bin (t : IntType) (op : IntBinOp) : SourceAllowed program memory rank module (.intBinOp t op)
  | call {i : FuncIdx} {a : FuncAddr} {fn : Function}
      (resolved : module.funcs[i.toNat]? = some a) (found : program.lookup a = some fn)
      (decreases : fn.rank < rank) : SourceAllowed program memory rank module (.call i)
  | load (offset : Fin (2 ^ 32)) (slot : module.memories[0]? = some memory) :
      SourceAllowed program memory rank module (.intLoad .i32 none (immediate offset))
  | store (offset : Fin (2 ^ 32)) (slot : module.memories[0]? = some memory) :
      SourceAllowed program memory rank module (.intStore .i32 none (immediate offset))
  | if_ {result : Option NumType} {left right : Wasm.V1.Expr}
      (thenBody : ∀ i ∈ left, SourceAllowed program memory rank module i)
      (elseBody : ∀ i ∈ right, SourceAllowed program memory rank module i) :
      SourceAllowed program memory rank module (.if_ result left right)
  -- Source blocks and selected conditional arms open the same kind of native label.
  | block {result : Option NumType} {body : Wasm.V1.Expr}
      (guard : ∀ i ∈ body, SourceAllowed program memory rank module i) :
      SourceAllowed program memory rank module (.block result body)
  | loop {result : Option NumType} {body : Wasm.V1.Expr}
      (guard : ∀ i ∈ body, SourceAllowed program memory rank module i) :
      SourceAllowed program memory rank module (.loop result body)
  | br (depth : LabelIdx) : SourceAllowed program memory rank module (.br depth)
  | brIf (depth : LabelIdx) : SourceAllowed program memory rank module (.brIf depth)
  | brTable (depths : List LabelIdx) (fallback : LabelIdx) :
      SourceAllowed program memory rank module (.brTable depths fallback)
  | unreachable : SourceAllowed program memory rank module .unreachable
  | return_ : SourceAllowed program memory rank module .return_

/-- The active module and rank are local to a frame. Label entry retains both.
An external caller may have its own module and an arbitrary rank ceiling. -/
inductive Allowed (program : Program) (memory : MemAddr) : Nat → ModuleInst → Admin → Prop where
  | source {rank module i} (guard : SourceAllowed program memory rank module i) :
      Allowed program memory rank module (.source i)
  | trap {rank module} : Allowed program memory rank module .trap
  | invoke {rank module address fn} (found : program.lookup address = some fn)
      (decreases : fn.rank < rank) : Allowed program memory rank module (.invoke address)
  | label {rank module n body} (scalar : n ≤ 1) (inside : ∀ x ∈ body, Allowed program memory rank module x) :
      Allowed program memory rank module (.label n [] body)
  | loopLabel {rank module result loopBody body}
      (restart : SourceAllowed program memory rank module (.loop result loopBody))
      (inside : ∀ x ∈ body, Allowed program memory rank module x) :
      Allowed program memory rank module (.label 0 [.loop result loopBody] body)
  | frame {rank module n callee body address fn} (found : program.lookup address = some fn)
      (decreases : fn.rank < rank) (scope : callee.module = fn.declaration.module)
      (arity : n = fn.declaration.results.length)
      (inside : ∀ x ∈ body, Allowed program memory fn.rank callee.module x) :
      Allowed program memory rank module (.frame n callee body)

abbrev CodeAllowed (program : Program) (memory : MemAddr) (rank : Nat) (module : ModuleInst)
    (code : List Admin) : Prop :=
  ∀ x ∈ code, Allowed program memory rank module x

def Ready (program : Program) (memory : MemAddr) (rank : Nat) (extent : Nat) (state : State) : Prop :=
  state.bytes.size = extent ∧ CodeAllowed program memory rank state.frame.module state.code

/-- One native administrative operation at a time. The frame and context
congruences thread the same bytes into and out of their premises. -/
inductive Edge (program : Program) (memory : MemAddr) : State → State → Prop where
  | pure {bytes f before after} (move : PureStep before after) :
      Edge program memory ⟨bytes, f, before⟩ ⟨bytes, f, after⟩
  | context {bytes bytes' f f' before after}
      (move : Edge program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩)
      (saved : List Value) (tail : List Admin) :
      Edge program memory ⟨bytes, f, values saved ++ before ++ tail⟩
        ⟨bytes', f', values saved ++ after ++ tail⟩
  | label {bytes bytes' f f' before after}
      (move : Edge program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩) (n : Nat) :
      Edge program memory ⟨bytes, f, [.label n [] before]⟩ ⟨bytes', f', [.label n [] after]⟩
  | underLoop {bytes bytes' f f' before after} (result : Option NumType) (body : Wasm.V1.Expr)
      (move : Edge program memory ⟨bytes, f, before⟩ ⟨bytes', f', after⟩) :
      Edge program memory ⟨bytes, f, [.label 0 [.loop result body] before]⟩
        ⟨bytes', f', [.label 0 [.loop result body] after]⟩
  | frame {bytes bytes' inner inner' before after}
      (move : Edge program memory ⟨bytes, inner, before⟩ ⟨bytes', inner', after⟩)
      (n : Nat) (outer : Frame) :
      Edge program memory ⟨bytes, outer, [.frame n inner before]⟩
        ⟨bytes', outer, [.frame n inner' after]⟩
  | get {bytes f i v} (found : f.locals[i.toNat]? = some v) :
      Edge program memory ⟨bytes, f, [.source (.localGet i)]⟩ ⟨bytes, f, [value v]⟩
  | set {bytes f i v old} (found : f.locals[i.toNat]? = some old) :
      Edge program memory ⟨bytes, f, [value v, .source (.localSet i)]⟩
        ⟨bytes, { f with locals := f.locals.set i.toNat v }, []⟩
  | resolve {bytes f i address} (found : f.module.funcs[i.toNat]? = some address) :
      Edge program memory ⟨bytes, f, [.source (.call i)]⟩ ⟨bytes, f, [.invoke address]⟩
  | enter {bytes f address fn args} (found : program.lookup address = some fn)
      (count : args.length = fn.declaration.params.length) :
      Edge program memory ⟨bytes, f, values args ++ [.invoke address]⟩
        ⟨bytes, f, [.frame fn.declaration.results.length (fn.declaration.frame args)
          [.label fn.declaration.results.length [] (expression fn.v1Func.body)]]⟩
  | load {bytes f arg address out} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryQuery.EdgeAt bytes arg.offset.val (.load address) out) :
      Edge program memory ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load address)⟩
        ⟨bytes, f, MemoryQuery.v1CodeAt arg out⟩
  | store {bytes f arg address word written} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryWrite.EdgeAt bytes arg.offset.val (.store address word) (.written written)) :
      Edge program memory ⟨bytes, f, [value (.int .i32 address), value (.int .i32 word),
        .source (.intStore .i32 none arg)]⟩ ⟨written, f, []⟩
  | storeTrap {bytes f arg address word} (slot : f.module.memories[0]? = some memory)
      (rule : MemoryWrite.EdgeAt bytes arg.offset.val (.store address word) .trap) :
      Edge program memory ⟨bytes, f, [value (.int .i32 address), value (.int .i32 word),
        .source (.intStore .i32 none arg)]⟩ ⟨bytes, f, [.trap]⟩

abbrev Runs (program : Program) (memory : MemAddr) := Relation.ReflTransGen (Edge program memory)

def render {H : Type} (base : Store H) (memory : MemAddr) (initial : MemInst) (state : State) :
    Config H :=
  ⟨storeWithBytes base memory initial state.bytes, state.frame, state.code⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
