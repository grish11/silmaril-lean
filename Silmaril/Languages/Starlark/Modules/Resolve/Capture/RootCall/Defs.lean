module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Functions
local notation "OperandSource" => Functions.Lowering.Resolve.SourceExpr
open Forwarding (Accepted Chain)
open Lists (Outcome State)
open Assignment (ReadResolves)

/-- A module segment can contain unrelated definitions in the checked
chain profile. Assignments and expression commands add no declarations. -/
inductive Segment (globals : List String) : List Command → Prop where
  | nil : Segment globals []
  | assign (name : String) (value : OperandSource) {rest : List Command} :
      Segment globals rest → Segment globals (.assign name value :: rest)
  | eval (value : OperandSource) {rest : List Command} :
      Segment globals rest → Segment globals (.eval value :: rest)
  | define (chain : Chain) {rest : List Command} :
      (∀ program : Program, Accepted globals program [] chain) → Segment globals rest →
      Segment globals (.define chain.name (.required chain.parameters) chain.body :: rest)
  | emit {name : String} {signature : SourceSignature} {body : Statement} {rest : List Command} :
      (∃ declaration, ∀ program, elaborateCommand ⟨⟨[], globals⟩, .global⟩
        (.define name signature body) program = .ok (.exec (.define name program.size), program.push declaration)) →
      Segment globals rest → Segment globals (.define name signature body :: rest)

  | emitPair {name : String} {signature : SourceSignature} {body : Statement} {rest : List Command} :
      (∃ (child : Declaration) (parent : Nat → Declaration), ∀ program,
        elaborateCommand ⟨⟨[], globals⟩, .global⟩ (.define name signature body) program =
          .ok (.exec (.define name (program.size + 1)), (program.push child).push (parent program.size))) →
      Segment globals rest → Segment globals (.define name signature body :: rest)

/-- The read-only call operands use the independently declared module
scope. An index has two ordered suboperands. -/
inductive Operand (globals : List String) : OperandSource → Lowering.Expr → Prop where
  | global {name : String} :
      name.toList.head? ≠ some '$' →
      ReadResolves ⟨[], [], globals⟩ name (.atom (.read (.bound (globalSlot name)))) [globalSlot name] →
      Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name))))
  | int (n : Int) : Operand globals (.scalar (.int n)) (.atom (.scalar (.int n)))
  | string (s : String) : Operand globals (.string s) (.atom (.string s))
  | index {source index : OperandSource} {resolved subscript : Lowering.Expr} :
      Operand globals source resolved → Operand globals index subscript →
      Operand globals (.index source index) (.index resolved subscript)

/-- Independent evaluation of a normalized operand. A failed receiver
skips the index expression. Reads use the checked value/store operations. -/
inductive Evaluates (state : State) : OperandSource → Outcome Lists.Value → Prop where
  | name (name : String) : Evaluates state (.scalar (.read name)) (state.read (.bound (globalSlot name)))
  | int (n : Int) : Evaluates state (.scalar (.int n)) (.ok (.scalar (.int n)) state)
  | string (s : String) : Evaluates state (.string s) (.ok (.string s) state)
  | index {source index : OperandSource} {value : Lists.Value} {out : Outcome Lists.Value} :
      Evaluates state source (.ok value state) → Evaluates state index out →
      Evaluates state (.index source index) (out.resume (Lists.readIndex value))
  | receiverError {source index : OperandSource} {error : Lists.Error} :
      Evaluates state source (.error error state) →
      Evaluates state (.index source index) (.error error state)

/-- The callee is the head of this spine. An error never reaches the
next operand, and positional binding begins after the entire spine. -/
inductive EvaluatesOperands (state : State) : List OperandSource → Outcome (List Lists.Value) → Prop where
  | nil : EvaluatesOperands state [] (.ok [] state)
  | cons {head : OperandSource} {tail : List OperandSource} {value : Lists.Value} {out : Outcome (List Lists.Value)} :
      Evaluates state head (.ok value state) → EvaluatesOperands state tail out →
      EvaluatesOperands state (head :: tail) (out.resume (fun values next => .ok (value :: values) next))
  | error {head : OperandSource} {tail : List OperandSource} {error : Lists.Error} :
      Evaluates state head (.error error state) → EvaluatesOperands state (head :: tail) (.error error state)

/-- Each source binding has its own module slot. This concerns slot
ownership rather than aliases in stored values. -/
@[expose] def DistinctOwned (state : State) : Prop :=
  ∀ a b address, state.slots a = some (.owned address) → state.slots b = some (.owned address) → a = b

/-- The live module binding identifies an installed closure by address. -/
structure Live (state : State) (name : String) (address : Lists.Address) (id : Nat)
    (captures : List Lists.Capture) (frozen : Bool)
    (defaults : List (Binding × Lists.Value) := []) : Prop where
  owned : ∃ slot, state.slots (globalSlot name) = some (.owned slot)
  binding : state.bindingValue (globalSlot name) = .ok (.function address)
  cell : state.heap[address]? = some ⟨.function ⟨id, captures, defaults⟩, frozen⟩

/-- A source segment of assignments to other globals, with successful
read-only operands. RHSs can read or copy the live closure. -/
inductive Writes (globals : List String) (callee : String) : State → List Command → List Modules.Command → State → Prop where
  | nil (state : State) : Writes globals callee state [] [] state
  | cons {state final : State} {name : String} {operand : OperandSource} {code : Lowering.Expr}
      {value : Lists.Value} {rest : List Command} {commands : List Modules.Command} :
      name ≠ callee → Operand globals operand code → Evaluates state operand (.ok value state) →
      Writes globals callee (state.write (globalSlot name) value) rest commands final →
      Writes globals callee state (.assign name operand :: rest) (.exec (.assignExpr name code) :: commands) final

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
