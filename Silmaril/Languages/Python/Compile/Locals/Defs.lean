module

public import Silmaril.Languages.Python.Core.Locals.Defs
public import Silmaril.Languages.Python.Source.Scope.Defs

/-! # Lowering one Python integer-local frame

The module contains one undecorated, parameterless function. Its core
artifact consists of scalar local assignments, terminal branches and returns.
Names are accepted only with the analyzed block's local access and a
matching slot witness.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Locals

abbrev Frame := Core.Locals.Code

def localNames (scope : Source.Scope) : List Source.Name :=
  scope.context.assigned.reverse.filter (fun name => decide (scope.access name = some .local))

structure Address (scope : Source.Scope) (name : Source.Name) where
  index : Fin (localNames scope).length
  lookup_eq : (localNames scope)[index] = name
  access_eq : scope.access name = some .local

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleShape
  | missingFunctionScope
  | bodyShape
  | expressionShape
  | unresolvedLocal (name : Source.Name)
  deriving BEq, DecidableEq, Repr

def address? (scope : Source.Scope) (name : Source.Name) : Option (Address scope name) :=
  if access : scope.access name = some .local then
    let selected := (localNames scope).findFinIdx? (fun candidate => decide (candidate = name))
    selected.pmap (p := fun index => selected = some index)
      (fun index found => ⟨index, of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1, access⟩)
      (fun _ found => Option.mem_def.mp found)
  else none

inductive OperatorTranslation : Source.BinaryOperator → Core.BinOp → Prop where
  | add : OperatorTranslation .add .add
  | floorDiv : OperatorTranslation .floorDiv .floorDiv

def operator? : (op : Source.BinaryOperator) → Option {target // OperatorTranslation op target}
  | .add => some ⟨.add, .add⟩
  | .floorDiv => some ⟨.floorDiv, .floorDiv⟩
  | _ => none

def logicalOperator : Source.BooleanOperator → Core.Locals.LogicalOp
  | .and_ => .and
  | .or_ => .or

mutual
  inductive RhsTranslation (scope : Source.Scope) :
      Source.Expr → Core.Locals.Rhs (localNames scope).length → Prop where
    | integer (value : Int) : RhsTranslation scope (.integer value) (.arithmetic (.int value))
    | name (name : Source.Name) (address : Address scope name) :
        RhsTranslation scope (.name name) (.read address.index)
    | binary {op : Source.BinaryOperator} {targetOp : Core.BinOp}
        {left right : Source.Expr} {lhs rhs : Core.Locals.Rhs (localNames scope).length}
        (operator : OperatorTranslation op targetOp)
        (leftTranslation : RhsTranslation scope left lhs)
        (rightTranslation : RhsTranslation scope right rhs) :
        RhsTranslation scope (.binary op left right) (.binary targetOp lhs rhs)
    | logical {op : Source.BooleanOperator} {first second rest target}
        (translated : OperandsTranslation scope op (first :: second :: rest) target) :
        RhsTranslation scope (.booleanOp op (first :: second :: rest)) target

  inductive OperandsTranslation (scope : Source.Scope) :
      Source.BooleanOperator → List Source.Expr → Core.Locals.Rhs (localNames scope).length → Prop where
    | last {op source target} (translated : RhsTranslation scope source target) :
        OperandsTranslation scope op [source] target
    | next {op first second rest lhs rhs} (head : RhsTranslation scope first lhs)
        (tail : OperandsTranslation scope op (second :: rest) rhs) :
        OperandsTranslation scope op (first :: second :: rest) (.logical (logicalOperator op) lhs rhs)
end

mutual
  def lowerRhs (scope : Source.Scope) : (source : Source.Expr) →
      Except Error {target // RhsTranslation scope source target}
    | .integer value => .ok ⟨.arithmetic (.int value), .integer value⟩
    | .name name =>
      match address? scope name with
      | none => .error (.unresolvedLocal name)
      | some address => .ok ⟨.read address.index, .name name address⟩
    | .binary op left right =>
      match operator? op with
      | none => .error .expressionShape
      | some ⟨targetOp, operator⟩ => do
        let lhs ← lowerRhs scope left
        let rhs ← lowerRhs scope right
        return ⟨.binary targetOp lhs.val rhs.val, .binary operator lhs.property rhs.property⟩
    | .booleanOp op (first :: second :: rest) => do
      let lowered ← lowerOperands scope op (first :: second :: rest)
      return ⟨lowered.val, .logical lowered.property⟩
    | _ => .error .expressionShape
  termination_by source => sizeOf source

  def lowerOperands (scope : Source.Scope) (op : Source.BooleanOperator) :
      (sources : List Source.Expr) → Except Error {target // OperandsTranslation scope op sources target}
    | [] => .error .expressionShape
    | [source] => do
      let lowered ← lowerRhs scope source
      return ⟨lowered.val, .last lowered.property⟩
    | first :: second :: rest => do
      let lhs ← lowerRhs scope first
      let rhs ← lowerOperands scope op (second :: rest)
      return ⟨.logical (logicalOperator op) lhs.val rhs.val, .next lhs.property rhs.property⟩
  termination_by sources => sizeOf sources
end

inductive Assignment : Source.Stmt → Source.Name → Source.Expr → Prop where
  | scalar (name : Source.Name) (value : Source.Expr) : Assignment (.assign name value) name value
  | singleTarget (name : Source.Name) (value : Source.Expr) :
      Assignment (.assignTargets [.name name] value) name value

def assignment? : (statement : Source.Stmt) →
    Option {pair : Source.Name × Source.Expr // Assignment statement pair.1 pair.2}
  | .assign name value => some ⟨(name, value), .scalar name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleTarget name value⟩
  | _ => none

inductive BodyTranslation (scope : Source.Scope) :
    List Source.Stmt → Frame (localNames scope).length → Prop where
  | ret {value : Source.Expr} {rhs : Core.Locals.Rhs (localNames scope).length}
      (translated : RhsTranslation scope value rhs) :
      BodyTranslation scope [.return_ (some value)] (.ret rhs)
  | assign {statement : Source.Stmt} {name : Source.Name} {value : Source.Expr}
      {rest : List Source.Stmt} {rhs : Core.Locals.Rhs (localNames scope).length}
      {next : Frame (localNames scope).length}
      (assignment : Assignment statement name value) (address : Address scope name)
      (translated : RhsTranslation scope value rhs) (remaining : BodyTranslation scope rest next) :
      BodyTranslation scope (statement :: rest) (.assign address.index rhs next)
  | branch {condition yes no test yesCode noCode}
      (translated : RhsTranslation scope condition test)
      (thenBranch : BodyTranslation scope yes yesCode) (elseBranch : BodyTranslation scope no noCode) :
      BodyTranslation scope [.if_ condition yes no] (.branch test yesCode noCode)

def lowerBody (scope : Source.Scope) : (body : List Source.Stmt) →
    Except Error {code // BodyTranslation scope body code}
  | [.return_ (some value)] => do
    let rhs ← lowerRhs scope value
    return ⟨.ret rhs.val, .ret rhs.property⟩
  | [.if_ condition yes no] => do
    let test ← lowerRhs scope condition
    let thenBranch ← lowerBody scope yes
    let elseBranch ← lowerBody scope no
    return ⟨.branch test.val thenBranch.val elseBranch.val,
      .branch test.property thenBranch.property elseBranch.property⟩
  | statement :: rest =>
    match assignment? statement with
    | none => .error .bodyShape
    | some ⟨(name, value), assignment⟩ =>
      match address? scope name with
      | none => .error (.unresolvedLocal name)
      | some address => do
        let rhs ← lowerRhs scope value
        let tail ← lowerBody scope rest
        return ⟨.assign address.index rhs.val tail.val,
          .assign assignment address rhs.property tail.property⟩
  | [] => .error .bodyShape
termination_by body => sizeOf body

structure Compiled (source : Source.Module) where
  name : Source.Name
  body : List Source.Stmt
  shape : source = ⟨[.functionDef name [] body [] none]⟩
  tree : Source.ScopeTree
  analyzed : Source.analyze source = .ok tree
  scope : Source.Scope
  located : tree.atPath [0] = some scope
  code : Frame (localNames scope).length
  translated : BodyTranslation scope body code

def compile (source : Source.Module) : Except Error (Compiled source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    match shape : source with
    | ⟨[.functionDef name [] body [] none]⟩ =>
      match located : tree.atPath [0] with
      | none => .error .missingFunctionScope
      | some scope =>
        (lowerBody scope body).map fun lowered =>
          ⟨name, body, rfl, tree, shape ▸ analyzed, scope, located, lowered.val, lowered.property⟩
    | _ => .error .moduleShape

end Silmaril.Languages.Python.Compile.Locals
