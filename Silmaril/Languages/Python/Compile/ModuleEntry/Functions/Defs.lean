module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

/-! # Lower module function bindings and positional call sites

The module plan preserves ordering between definitions, assignments and
calls. Reads from a function's module scope retain the resolved name for
runtime lookup in the module's current namespace.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

open Source (BlockPath Name Scope ScopeTree)
open Compile.Closure (frameLayout)
open Compile.Closure.Body (Code)

inductive CallExpression : Source.Expr → Name → List (Source.ArgumentKind × Source.Expr) → Prop where
  | plain (name : Name) (arguments : List Source.Expr) :
      CallExpression (.call (.name name) arguments) name (arguments.map (.positional, ·))
  | tagged (name : Name) (arguments : List (Source.ArgumentKind × Source.Expr)) :
      CallExpression (.callWith (.name name) arguments) name arguments

def callExpression? : (source : Source.Expr) →
    Option {result : Name × List (Source.ArgumentKind × Source.Expr) // CallExpression source result.1 result.2}
  | .call (.name name) arguments => some ⟨(name, arguments.map (.positional, ·)), .plain name arguments⟩
  | .callWith (.name name) arguments => some ⟨(name, arguments), .tagged name arguments⟩
  | _ => none

inductive CallSite : Source.Stmt → Option Name → Name → List (Source.ArgumentKind × Source.Expr) → Prop where
  | discard {value callee arguments} (call : CallExpression value callee arguments) :
      CallSite (.expression value) none callee arguments
  | assign {source name value callee arguments} (binding : Binding source name value)
      (call : CallExpression value callee arguments) : CallSite source (some name) callee arguments

def callSite? : (source : Source.Stmt) →
    Option {result : Option Name × Name × List (Source.ArgumentKind × Source.Expr) //
      CallSite source result.1 result.2.1 result.2.2}
  | .expression value =>
    (callExpression? value).map fun ⟨(name, arguments), call⟩ => ⟨(none, name, arguments), .discard call⟩
  | source => do
    let ⟨(target, value), binding⟩ ← binding? source
    let ⟨(name, arguments), call⟩ ← callExpression? value
    return ⟨(some target, name, arguments), .assign binding call⟩

inductive Destination (scope : Scope) where
  | discard
  | store (name : Name) (reference : GlobalReference scope name)

def Destination.name? {scope : Scope} : Destination scope → Option Name
  | .discard => none
  | .store name _ => some name

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleScope
  | scalar (error : ModuleEntry.Error)
  | functionBody (error : Compile.Closure.Body.Error)
  | functionScope (path : BlockPath)
  | argumentProfile
  | unresolvedGlobal (name : Name)
  deriving Repr

def lowerDestination (scope : Scope) : (name : Option Name) →
    Except Error {target : Destination scope // target.name? = name}
  | none => .ok ⟨.discard, rfl⟩
  | some name => do
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    return ⟨.store name reference, rfl⟩

inductive Positional (scope : Scope) :
    List (Source.ArgumentKind × Source.Expr) → List (Operand scope) → Prop where
  | nil : Positional scope [] []
  | cons {source operand rest targets} (first : OperandTranslation scope source operand)
      (tail : Positional scope rest targets) :
      Positional scope ((.positional, source) :: rest) (operand :: targets)

def lowerArguments (scope : Scope) : (source : List (Source.ArgumentKind × Source.Expr)) →
    Except Error {target // Positional scope source target}
  | [] => .ok ⟨[], .nil⟩
  | (.positional, expression) :: rest => do
    let operand ← (lowerOperand scope expression).mapError .scalar
    let tail ← lowerArguments scope rest
    return ⟨operand.val :: tail.val, .cons operand.property tail.property⟩
  | _ => .error .argumentProfile

inductive Action (scope : Scope) where
  | scalar (action : ModuleEntry.Action scope)
  | define (name : Name) (reference : GlobalReference scope name) (child : ScopeTree)
      (parameters : Core.Closure.Parameters (frameLayout child.scope)) (code : Code (frameLayout child.scope))
  | call (destination : Destination scope) (name : Name) (reference : GlobalReference scope name)
      (arguments : List (Operand scope))

inductive Translation (tree : ScopeTree) : Nat → List Source.Stmt → List (Action tree.scope) → Prop where
  | done {index} (covered : index = tree.children.length) : Translation tree index [] []
  | scalar {index statement rest actions tail}
      (first : ModuleEntry.Translation tree.scope [statement] actions) (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (actions.map .scalar ++ tail)
  | call {index statement rest target name arguments destination reference values tail}
      (site : CallSite statement target name arguments) (result : destination.name? = target)
      (operandOrder : Positional tree.scope arguments values) (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (.call destination name reference values :: tail)
  | define {index name declaration body rest child reference parameters code tail}
      (located : tree.children[index]? = some child)
      (path : child.scope.context.path = tree.scope.context.path ++ [index])
      (kind : child.scope.context.kind = .function)
      (fixed : declaration.all Compile.Closure.Body.fixed = true)
      (parameterOrder : parameters.slots.map (Compile.Closure.parameterName child.scope) =
        declaration.map Source.Parameter.name)
      (functionBody : Compile.Closure.Body.Translation child 0 body code)
      (remaining : Translation tree (index + 1) rest tail) :
      Translation tree index (.functionDef name declaration body [] none :: rest)
        (.define name reference child parameters code :: tail)

def lowerPlan (tree : ScopeTree) (index : Nat) : (source : List Source.Stmt) →
    Except Error {actions // Translation tree index source actions}
  | [] =>
    if covered : index = tree.children.length then .ok ⟨[], .done covered⟩
    else .error (.functionScope tree.scope.context.path)
  | .functionDef name declaration body [] none :: rest => do
    let path := tree.scope.context.path ++ [index]
    match located : tree.children[index]? with
    | none => throw (.functionScope path)
    | some child =>
      if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
        let some reference := globalReference? tree.scope name | throw (.unresolvedGlobal name)
        let parameters ← (Compile.Closure.Body.checkParameters child.scope declaration).mapError .functionBody
        let code ← (Compile.Closure.Body.lowerBodyWith child true 0 body).mapError .functionBody
        let tail ← lowerPlan tree (index + 1) rest
        return ⟨.define name reference child parameters.val code.val :: tail.val,
          .define located scopeMatches.1 scopeMatches.2 parameters.property.1 parameters.property.2
            code.property tail.property⟩
      else throw (.functionScope path)
  | statement :: rest => do
    if let some ⟨(target, name, arguments), site⟩ := callSite? statement then
      let destination ← lowerDestination tree.scope target
      let some reference := globalReference? tree.scope name | throw (.unresolvedGlobal name)
      let operands ← lowerArguments tree.scope arguments
      let tail ← lowerPlan tree index rest
      return ⟨.call destination.val name reference operands.val :: tail.val,
        .call site destination.property operands.property tail.property⟩
    else
      let first ← (lowerStatements tree.scope [statement]).mapError .scalar
      let tail ← lowerPlan tree index rest
      return ⟨first.val.map .scalar ++ tail.val, .scalar first.property tail.property⟩

structure Checked (source : Source.Module) where
  tree : ScopeTree
  analyzed : Source.analyze source = .ok tree
  moduleScope : tree.scope.context.kind = .module_
  actions : List (Action tree.scope)
  lowered : Translation tree 0 source.body actions

def check (source : Source.Module) : Except Error (Checked source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    if kind : tree.scope.context.kind = .module_ then
      (lowerPlan tree 0 source.body).map fun lower =>
        ⟨tree, analyzed, kind, lower.val, lower.property⟩
    else .error .moduleScope

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
