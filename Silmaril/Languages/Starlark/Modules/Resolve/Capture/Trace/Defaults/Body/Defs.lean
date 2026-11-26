module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Functions
open Assignment (LexicalBlock ReadResolves)
open Lists (State Outcome Address Cell)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- A straight-line body of lexical name assignments and a final
return. The bounded operands are read-only apart from list allocation. -/
inductive Suite where
  | ret (value : Expr)
  | assign (name : String) (value : Expr) (rest : Suite)

@[expose] def Suite.source : Suite → Statement
  | .ret value => .ret (some value)
  | .assign name value rest => .seq (.assign name value) rest.source

@[expose] def Suite.binders : Suite → List String
  | .ret _ => []
  | .assign name _ rest => name :: rest.binders

/-- Static operand rules identify the lexical slot and preserve read
order. A singleton list uses the same checked display as other bodies. -/
inductive Operand (block : LexicalBlock) : Expr → Lowering.Expr → List Binding → Prop where
  | read {name : String} {binding : Binding} {origin : Origin} :
      name.toList.head? ≠ some '$' →
      ReadResolves block name (Leaf.readOperand binding) [binding] →
      ReadOrigin block binding origin →
      Operand block (.scalar (.read name)) (Leaf.readOperand binding) [binding]
  | int (value : Int) : Operand block (.scalar (.int value)) (.atom (.scalar (.int value))) []
  | index {receiver subscript : Expr} {recv sub : Lowering.Expr} {first second : List Binding} :
      Operand block receiver recv first → Operand block subscript sub second →
      Operand block (.index receiver subscript) (.index recv sub) (first ++ second)
  | list {element : Expr} {code : Lowering.Expr} {reads : List Binding} :
      Operand block element code reads → Operand block (.list [element]) (.list [code]) reads

inductive Elaborates (block : LexicalBlock) : Suite → Functions.Body → List Binding → Prop where
  | ret {source : Expr} {code : Lowering.Expr} {reads : List Binding} :
      Operand block source code reads → Elaborates block (.ret source) (.returnExpr code) reads
  | assign {name : String} {source : Expr} {rest : Suite} {code : Lowering.Expr} {tail : Functions.Body}
      {reads remaining : List Binding} :
      name ∈ block.owned → Operand block source code reads → Elaborates block rest tail remaining →
      Elaborates block (.assign name source rest) (.seq (.assignExpr (fileSlot name) code) tail) (reads ++ remaining)

/-- Source evaluation steps are ordered independently of the evaluator.
The binding read consults the reached heap, including an unbound slot. -/
inductive Evaluates (block : LexicalBlock) : State → Expr → Lowering.Expr → Outcome Value → Prop where
  | read {state : State} {name : String} {binding : Binding} :
      ReadResolves block name (Leaf.readOperand binding) [binding] →
      Evaluates block state (.scalar (.read name)) (Leaf.readOperand binding) (state.read (.bound binding))
  | int {state : State} (value : Int) :
      Evaluates block state (.scalar (.int value)) (.atom (.scalar (.int value))) (.ok (.scalar (.int value)) state)
  | index {state middle : State} {receiver subscript : Expr} {recv sub : Lowering.Expr}
      {value : Value} {out : Outcome Value} :
      Evaluates block state receiver recv (.ok value middle) → Evaluates block middle subscript sub out →
      Evaluates block state (.index receiver subscript) (.index recv sub) (out.resume (Lists.readIndex value))
  | receiverError {state final : State} {receiver subscript : Expr} {recv sub : Lowering.Expr} {error : Lists.Error} :
      Evaluates block state receiver recv (.error error final) →
      Evaluates block state (.index receiver subscript) (.index recv sub) (.error error final)
  | list {state : State} {element : Expr} {code : Lowering.Expr} {out : Outcome Value} :
      Evaluates block state element code out →
      Evaluates block state (.list [element]) (.list [code]) (out.resume fun value => Lists.allocate [value])

inductive Runs (block : LexicalBlock) : State → Suite → Functions.Body → Outcome Flow → Prop where
  | ret {state : State} {expression : Expr} {code : Lowering.Expr} {out : Outcome Value} :
      Evaluates block state expression code out →
      Runs block state (.ret expression) (.returnExpr code) (out.resume fun value next => .ok (.returned value) next)
  | assign {state middle : State} {name : String} {expression : Expr} {rest : Suite}
      {code : Lowering.Expr} {tail : Functions.Body} {value : Value} {out : Outcome Flow} :
      Evaluates block state expression code (.ok value middle) →
      Runs block (middle.write (fileSlot name) value) rest tail out →
      Runs block state (.assign name expression rest) (.seq (.assignExpr (fileSlot name) code) tail) out
  | assignError {state final : State} {name : String} {expression : Expr} {rest : Suite}
      {code : Lowering.Expr} {tail : Functions.Body} {error : Lists.Error} :
      Evaluates block state expression code (.error error final) →
      Runs block state (.assign name expression rest) (.seq (.assignExpr (fileSlot name) code) tail) (.error error final)

/-- Owned locals are fresh even when still unbound. Captured names keep
their original address in the caller heap. Both point to live binding cells. -/
structure Frame (block : LexicalBlock) (free : List FreeName) (floor : Nat) (state : State) : Prop where
  owned : ∀ name ∈ block.owned, ∃ address value frozen, floor ≤ address ∧
    state.slots (fileSlot name) = some (.owned address) ∧ state.heap[address]? = some ⟨.binding value, frozen⟩
  captured : ∀ binding, (⟨binding, binding⟩ : FreeName) ∈ free →
    ∃ address value frozen, address < floor ∧
      state.slots binding = some (.captured address (binding.scope == .local)) ∧
      state.heap[address]? = some ⟨.binding value, frozen⟩

/-- Successful or failed body steps preserve caller cells below the
activation's allocation boundary and keep the same slot addresses. -/
@[expose] def Keeps (floor : Nat) (first next : State) : Prop :=
  next.slots = first.slots ∧
  ∀ (address : Nat) (cell : Cell), address < floor → first.heap[address]? = some cell → next.heap[address]? = some cell

/-- An escaped closure carries selected addresses into later callers.
The cells still exist even when the defining activation is inactive. -/
@[expose] def CaptureCells (state : State) (captures : List Lists.Capture) : Prop :=
  ∀ capture ∈ captures, ∃ value frozen, state.heap[capture.address]? = some ⟨.binding value, frozen⟩

/-- This definition uses the existing plain positional defaults, with
the new body elaboration and capture selection. -/
structure Definition where
  name : String
  parameters : Defaults.Parameters
  body : Suite

@[expose] def Definition.command (definition : Definition) : Command :=
  .define definition.name definition.parameters.source definition.body.source

structure Plan (globals : List String) (definition : Definition) (enclosing : List String := []) where
  locals : List String
  code : Functions.Body
  reads : List Binding
  free : List FreeName
  binders : Block.LocalBinders definition.parameters.names definition.body.binders locals
  elaborates : Elaborates ⟨definition.parameters.names ++ locals, enclosing, globals⟩ definition.body code reads
  selects : Selects ⟨definition.parameters.names ++ locals, enclosing, globals⟩ reads free

@[expose] def Plan.block {globals : List String} {definition : Definition} {enclosing : List String}
    (plan : Plan globals definition enclosing) : LexicalBlock :=
  ⟨definition.parameters.names ++ plan.locals, enclosing, globals⟩

@[expose] def Plan.declaration {globals : List String} {definition : Definition} {enclosing : List String}
    (plan : Plan globals definition enclosing)
    (codes : List Lowering.Expr) : Declaration :=
  ⟨definition.parameters.signature codes, plan.locals.map fileSlot, plan.free, plan.code⟩

structure Admitted (globals : List String) (definition : Definition) : Prop where
  defaults : ∀ item ∈ definition.parameters.optional, Trace.Initializer globals item.2
  body : Nonempty (Plan globals definition)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
