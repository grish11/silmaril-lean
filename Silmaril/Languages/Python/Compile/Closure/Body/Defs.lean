module

public import Silmaril.Languages.Python.Compile.Closure.Thms

/-! # Source closure bodies awaiting code linking

The fixed positional profile lowers nested declarations, name reads and
writes, integer addition and calls. A child declaration retains its
analyzed path, distinct parameter destinations and ordered capture
operands so a code linker can choose the numeric key.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Body

open Source (BlockPath Name Scope ScopeTree)
open Core.Closure (CaptureSlot Parameters Slot)

inductive Expr (layout : Core.Closure.Layout) where
  | integer (value : Int)
  | read (slot : Slot layout)
  | add (left right : Expr layout)
  | call (callee : Expr layout) (arguments : List (Expr layout))
  deriving Repr

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleShape
  | bodyShape
  | expressionShape
  | argumentProfile
  | unresolvedName (name : Name)
  | parameterProfile
  | parameterLayout (path : BlockPath)
  | scopeTree (path : BlockPath)
  | captureLayout (path : BlockPath)
  deriving Repr

mutual
  inductive ExprTranslation (scope : Scope) : Source.Expr → Expr (frameLayout scope) → Prop where
    | integer (value : Int) : ExprTranslation scope (.integer value) (.integer value)
    | read {name : Name} {slot : Slot (frameLayout scope)}
        (translated : SlotTranslation scope name slot) : ExprTranslation scope (.name name) (.read slot)
    | add {left right lhs rhs} (leftTranslation : ExprTranslation scope left lhs)
        (rightTranslation : ExprTranslation scope right rhs) :
        ExprTranslation scope (.binary .add left right) (.add lhs rhs)
    | call {callee arguments targetCallee targetArguments}
        (function : ExprTranslation scope callee targetCallee)
        (positional : ArgumentsTranslation scope arguments targetArguments) :
        ExprTranslation scope (.call callee arguments) (.call targetCallee targetArguments)
    | callWith {callee arguments targetCallee targetArguments}
        (function : ExprTranslation scope callee targetCallee)
        (positional : TaggedArgumentsTranslation scope arguments targetArguments) :
        ExprTranslation scope (.callWith callee arguments) (.call targetCallee targetArguments)

  inductive ArgumentsTranslation (scope : Scope) :
      List Source.Expr → List (Expr (frameLayout scope)) → Prop where
    | nil : ArgumentsTranslation scope [] []
    | cons {source sources target targets} (first : ExprTranslation scope source target)
        (rest : ArgumentsTranslation scope sources targets) :
        ArgumentsTranslation scope (source :: sources) (target :: targets)

  inductive TaggedArgumentsTranslation (scope : Scope) :
      List (Source.ArgumentKind × Source.Expr) → List (Expr (frameLayout scope)) → Prop where
    | nil : TaggedArgumentsTranslation scope [] []
    | cons {source sources target targets} (first : ExprTranslation scope source target)
        (rest : TaggedArgumentsTranslation scope sources targets) :
        TaggedArgumentsTranslation scope ((.positional, source) :: sources) (target :: targets)
end

def lowerSlot (scope : Scope) (name : Name) :
    Except Error {slot // SlotTranslation scope name slot} := do
  let some result := slot? scope name | throw (.unresolvedName name)
  return result

mutual
  def lowerExpr (scope : Scope) : (source : Source.Expr) →
      Except Error {target // ExprTranslation scope source target}
    | .integer value => .ok ⟨.integer value, .integer value⟩
    | .name name => do
      let slot ← lowerSlot scope name
      return ⟨.read slot.val, .read slot.property⟩
    | .binary .add left right => do
      let lhs ← lowerExpr scope left
      let rhs ← lowerExpr scope right
      return ⟨.add lhs.val rhs.val, .add lhs.property rhs.property⟩
    | .call callee arguments => do
      let function ← lowerExpr scope callee
      let positional ← lowerArguments scope arguments
      return ⟨.call function.val positional.val, .call function.property positional.property⟩
    | .callWith callee arguments => do
      let function ← lowerExpr scope callee
      let positional ← lowerTaggedArguments scope arguments
      return ⟨.call function.val positional.val, .callWith function.property positional.property⟩
    | _ => .error .expressionShape
  termination_by source => sizeOf source

  def lowerArguments (scope : Scope) : (sources : List Source.Expr) →
      Except Error {targets // ArgumentsTranslation scope sources targets}
    | [] => .ok ⟨[], .nil⟩
    | source :: rest => do
      let first ← lowerExpr scope source
      let tail ← lowerArguments scope rest
      return ⟨first.val :: tail.val, .cons first.property tail.property⟩
  termination_by sources => sizeOf sources

  def lowerTaggedArguments (scope : Scope) : (sources : List (Source.ArgumentKind × Source.Expr)) →
      Except Error {targets // TaggedArgumentsTranslation scope sources targets}
    | [] => .ok ⟨[], .nil⟩
    | (.positional, source) :: rest => do
      let first ← lowerExpr scope source
      let tail ← lowerTaggedArguments scope rest
      return ⟨first.val :: tail.val, .cons first.property tail.property⟩
    | _ => .error .argumentProfile
  termination_by sources => sizeOf sources
end

/-- Path references are resolved by a later code linker. Both the call
arguments and the capture operands retain their source order. -/
inductive Code : Core.Closure.Layout → Type where
  | ret {layout} (value : Expr layout) : Code layout
  | assign {layout} (destination : Slot layout) (value : Expr layout) (next : Code layout) : Code layout
  | closure {layout} (destination : Slot layout) (path : BlockPath) (childLayout : Core.Closure.Layout)
      (parameters : Parameters childLayout) (captures : Fin childLayout.captures → CaptureSlot layout)
      (child : Code childLayout) (next : Code layout) : Code layout

/-- Child code paths in lexical preorder. -/
def Code.childPaths {layout : Core.Closure.Layout} : Code layout → List BlockPath
  | .ret _ => []
  | .assign _ _ next => next.childPaths
  | .closure _ path _ _ _ child next => path :: (child.childPaths ++ next.childPaths)

def fixed (parameter : Source.Parameter) : Bool :=
  parameter.defaultValue.isNone && parameter.annotation.isNone &&
    match parameter.kind with
    | .positionalOnly | .positionalOrKeyword => true
    | _ => false

def checkParameters (scope : Scope) (declaration : List Source.Parameter) :
    Except Error {target : Parameters (frameLayout scope) // declaration.all fixed = true ∧
      target.slots.map (parameterName scope) = declaration.map Source.Parameter.name} := do
  if profile : declaration.all fixed = true then
    if names : scope.context.parameters = declaration.map Source.Parameter.name then
      let some checked := Source.Closure.Frame.parameterLayout? scope
        | throw (.parameterLayout scope.context.path)
      return ⟨parameters checked, profile, (parameters_order checked).trans names⟩
    else throw (.scopeTree scope.context.path)
  else throw .parameterProfile

inductive Assignment : Source.Stmt → Name → Source.Expr → Prop where
  | simple (name : Name) (value : Source.Expr) : Assignment (.assign name value) name value
  | singleTarget (name : Name) (value : Source.Expr) : Assignment (.assignTargets [.name name] value) name value

def assignment? : (source : Source.Stmt) →
    Option {binding : Name × Source.Expr // Assignment source binding.1 binding.2}
  | .assign name value => some ⟨(name, value), .simple name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleTarget name value⟩
  | _ => none

inductive Translation : (tree : ScopeTree) → Nat → List Source.Stmt →
    Code (frameLayout tree.scope) → Prop where
  | ret {tree index source target} (complete : index = tree.children.length)
      (value : ExprTranslation tree.scope source target) :
      Translation tree index [.return_ (some source)] (.ret target)
  | assign {tree index statement name source rest slot target next}
      (assignment : Assignment statement name source) (destination : SlotTranslation tree.scope name slot)
      (value : ExprTranslation tree.scope source target) (tail : Translation tree index rest next) :
      Translation tree index (statement :: rest) (.assign slot target next)
  | nonlocal {tree index names rest next} (tail : Translation tree index rest next) :
      Translation tree index (.nonlocalDecl names :: rest) next
  | closure {tree index name declaration body rest slot child parameters code next}
      (found : tree.children[index]? = some child)
      (path : child.scope.context.path = tree.scope.context.path ++ [index])
      (kind : child.scope.context.kind = .function)
      (destination : SlotTranslation tree.scope name slot)
      (fixedPosition : declaration.all fixed = true)
      (parameterOrder : parameters.slots.map (parameterName child.scope) = declaration.map Source.Parameter.name)
      (captures : Source.Closure.Layout tree.scope child.scope.captures)
      (translated : Translation child 0 body code) (tail : Translation tree (index + 1) rest next) :
      Translation tree index (.functionDef name declaration body [] none :: rest)
        (.closure slot (tree.scope.context.path ++ [index]) (frameLayout child.scope) parameters
          (captureOperands captures) code next)

def lowerBody (tree : ScopeTree) (childIndex : Nat) : (body : List Source.Stmt) →
    Except Error {target // Translation tree childIndex body target}
  | [.return_ (some value)] => do
    if complete : childIndex = tree.children.length then
      let target ← lowerExpr tree.scope value
      return ⟨.ret target.val, .ret complete target.property⟩
    else throw (.scopeTree tree.scope.context.path)
  | .nonlocalDecl _ :: rest => do
    let tail ← lowerBody tree childIndex rest
    return ⟨tail.val, .nonlocal tail.property⟩
  | .functionDef name declaration body [] none :: rest => do
    let path := tree.scope.context.path ++ [childIndex]
    match found : tree.children[childIndex]? with
    | none => throw (.scopeTree path)
    | some child =>
      if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
        let destination ← lowerSlot tree.scope name
        let parameterSlots ← checkParameters child.scope declaration
        let some captures := Source.Closure.layout? tree.scope child.scope.captures | throw (.captureLayout path)
        let code ← lowerBody child 0 body
        let next ← lowerBody tree (childIndex + 1) rest
        return ⟨.closure destination.val path (frameLayout child.scope) parameterSlots.val
          (captureOperands captures) code.val next.val,
          .closure found scopeMatches.1 scopeMatches.2 destination.property parameterSlots.property.1
            parameterSlots.property.2 captures code.property next.property⟩
      else throw (.scopeTree path)
  | statement :: rest => do
    let some ⟨(name, value), assignment⟩ := assignment? statement | throw .bodyShape
    let destination ← lowerSlot tree.scope name
    let target ← lowerExpr tree.scope value
    let next ← lowerBody tree childIndex rest
    return ⟨.assign destination.val target.val next.val,
      .assign assignment destination.property target.property next.property⟩
  | [] => .error .bodyShape
termination_by body => sizeOf body

structure Compiled (source : Source.Module) where
  name : Name
  declaration : List Source.Parameter
  body : List Source.Stmt
  shape : source.body = [.functionDef name declaration body [] none]
  tree : ScopeTree
  moduleTree : ScopeTree
  analyzed : Source.analyze source = .ok moduleTree
  located : moduleTree.children = [tree]
  parameters : Parameters (frameLayout tree.scope)
  fixedPosition : declaration.all fixed = true
  parameterOrder : parameters.slots.map (parameterName tree.scope) = declaration.map Source.Parameter.name
  code : Code (frameLayout tree.scope)
  translated : Translation tree 0 body code

def Compiled.paths {source : Source.Module} (compiled : Compiled source) : List BlockPath :=
  compiled.tree.scope.context.path :: compiled.code.childPaths

def compile (source : Source.Module) : Except Error (Compiled source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    match shape : source.body, located : tree.children with
    | [.functionDef name declaration body [] none], [entry] => do
      let parameters ← checkParameters entry.scope declaration
      let code ← lowerBody entry 0 body
      return ⟨name, declaration, body, shape, entry, tree, analyzed, located, parameters.val,
        parameters.property.1, parameters.property.2, code.val, code.property⟩
    | _, _ => .error .moduleShape

end Silmaril.Languages.Python.Compile.Closure.Body
