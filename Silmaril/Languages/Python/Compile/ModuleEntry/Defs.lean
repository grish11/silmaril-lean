module

public import Silmaril.Languages.Python.Source.Scope.Defs

/-! # Check Python module-entry syntax and global name bindings

This source profile keeps name keys for global reads and writes and
retains message-free assertions in execution order. Each reference records
the analyzed access. The plan is independent of a runtime store.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry

open Source (Access Expr Name Scope ScopeTree Stmt)

structure GlobalReference (scope : Scope) (name : Name) where
  access : Access
  resolved : scope.access name = some access
  globalAccess : access = .moduleName ∨ access = .declaredGlobal

def globalReference? (scope : Scope) (name : Name) : Option (GlobalReference scope name) :=
  if moduleName : scope.access name = some .moduleName then
    some ⟨.moduleName, moduleName, Or.inl rfl⟩
  else if declared : scope.access name = some .declaredGlobal then
    some ⟨.declaredGlobal, declared, Or.inr rfl⟩
  else none

inductive Operand (scope : Scope) where
  | integer (value : Int)
  | read (name : Name) (reference : GlobalReference scope name)

inductive OperandTranslation (scope : Scope) : Expr → Operand scope → Prop where
  | integer (value : Int) : OperandTranslation scope (.integer value) (.integer value)
  | read (name : Name) (reference : GlobalReference scope name) :
      OperandTranslation scope (.name name) (.read name reference)

inductive Action (scope : Scope) where
  | assign (name : Name) (reference : GlobalReference scope name) (value : Operand scope)
  | assertion (condition : Operand scope)

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleScope
  | unresolvedGlobal (name : Name)
  | expressionProfile
  | assertionMessage
  | statementProfile
  deriving BEq, DecidableEq, Repr

def lowerOperand (scope : Scope) : (source : Expr) → Except Error {value // OperandTranslation scope source value}
  | .integer value => .ok ⟨.integer value, .integer value⟩
  | .name name => do
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    return ⟨.read name reference, .read name reference⟩
  | _ => .error .expressionProfile

inductive Binding : Stmt → Name → Expr → Prop where
  | direct (name : Name) (value : Expr) : Binding (.assign name value) name value
  | singleton (name : Name) (value : Expr) : Binding (.assignTargets [.name name] value) name value

def binding? : (statement : Stmt) → Option {pair : Name × Expr // Binding statement pair.1 pair.2}
  | .assign name value => some ⟨(name, value), .direct name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleton name value⟩
  | _ => none

inductive Translation (scope : Scope) : List Stmt → List (Action scope) → Prop where
  | done : Translation scope [] []
  | assign {statement name expression reference value rest next}
      (binding : Binding statement name expression)
      (operand : OperandTranslation scope expression value) (tail : Translation scope rest next) :
      Translation scope (statement :: rest) (.assign name reference value :: next)
  | assertion {expression test rest next}
      (operand : OperandTranslation scope expression test) (tail : Translation scope rest next) :
      Translation scope (.assert_ expression none :: rest) (.assertion test :: next)
  | globals {names rest next} (tail : Translation scope rest next) :
      Translation scope (.globalDecl names :: rest) next
  | pass {rest next} (tail : Translation scope rest next) :
      Translation scope (.pass :: rest) next

def lowerStatements (scope : Scope) : (body : List Stmt) →
    Except Error {actions // Translation scope body actions}
  | [] => .ok ⟨[], .done⟩
  | .assert_ condition none :: body => do
    let test ← lowerOperand scope condition
    let tail ← lowerStatements scope body
    return ⟨.assertion test.val :: tail.val, .assertion test.property tail.property⟩
  | .assert_ _ (some _) :: _ => .error .assertionMessage
  | .globalDecl _ :: body => do
    let tail ← lowerStatements scope body
    return ⟨tail.val, .globals tail.property⟩
  | .pass :: body => do
    let tail ← lowerStatements scope body
    return ⟨tail.val, .pass tail.property⟩
  | statement :: body => do
    let some ⟨(name, expression), binding⟩ := binding? statement | throw .statementProfile
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    let value ← lowerOperand scope expression
    let tail ← lowerStatements scope body
    return ⟨.assign name reference value.val :: tail.val, .assign binding value.property tail.property⟩

structure Checked (source : Source.Module) where
  tree : ScopeTree
  analyzed : Source.analyze source = .ok tree
  moduleScope : tree.scope.context.kind = .module_
  actions : List (Action tree.scope)
  lowered : Translation tree.scope source.body actions

def check (source : Source.Module) : Except Error (Checked source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    if kind : tree.scope.context.kind = .module_ then
      (lowerStatements tree.scope source.body).map fun lowering =>
        ⟨tree, analyzed, kind, lowering.val, lowering.property⟩
    else .error .moduleScope

end Silmaril.Languages.Python.Compile.ModuleEntry
