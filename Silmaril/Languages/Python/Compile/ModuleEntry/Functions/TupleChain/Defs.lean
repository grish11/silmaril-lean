module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

open Source (Scope)

inductive TupleOperand (scope : Scope) where
  | literal (contents : List Core.Module.TupleDispatch.Element)
  | global (name : String) (reference : GlobalReference scope name)
  | add (left right : List Core.Module.TupleDispatch.Element)
  | boundAdd (receiver argument : List Core.Module.TupleDispatch.Element)
  | unboundAdd (reference : GlobalReference scope "tuple") (receiver argument : List Core.Module.TupleDispatch.Element)

  | construct (reference : GlobalReference scope "tuple") (argument : Option (List Core.Module.TupleDispatch.Element))
  | constructGlobal (reference : GlobalReference scope "tuple") (name : String)
      (argument : GlobalReference scope name)

def TupleOperand.usesCall {scope : Scope} : TupleOperand scope → Bool
  | .literal _ | .global .. | .add .. => false
  | .boundAdd .. | .unboundAdd .. | .construct .. | .constructGlobal .. => true

inductive TupleAddCall : Source.Expr → Source.Expr → List (Source.ArgumentKind × Source.Expr) → Prop where
  | plain (receiver arguments) :
      TupleAddCall (.call (.attribute receiver "__add__") arguments) receiver
        (arguments.map (.positional, ·))
  | tagged (receiver arguments) :
      TupleAddCall (.callWith (.attribute receiver "__add__") arguments) receiver arguments

def tupleAddCall? : (source : Source.Expr) →
    Option {shape : Source.Expr × List (Source.ArgumentKind × Source.Expr) //
      TupleAddCall source shape.1 shape.2}
  | .call (.attribute receiver "__add__") arguments =>
    some ⟨(receiver, arguments.map (.positional, ·)), .plain receiver arguments⟩
  | .callWith (.attribute receiver "__add__") arguments =>
    some ⟨(receiver, arguments), .tagged receiver arguments⟩
  | _ => none

inductive TupleConstructorCall : Source.Expr → List (Source.ArgumentKind × Source.Expr) → Prop where
  | plain (arguments) :
      TupleConstructorCall (.call (.name "tuple") arguments) (arguments.map (.positional, ·))
  | tagged (arguments) :
      TupleConstructorCall (.callWith (.name "tuple") arguments) arguments

def tupleConstructorCall? :
    (source : Source.Expr) → Option {arguments // TupleConstructorCall source arguments}
  | .call (.name "tuple") arguments => some ⟨_, .plain arguments⟩
  | .callWith (.name "tuple") arguments => some ⟨arguments, .tagged arguments⟩
  | _ => none

def tupleScalar? : Source.Expr → Option Core.Module.Value
  | .none_ => some .none
  | source => scalarLiteral? source

def scalarTupleElements? (source : Source.Expr) : Option (List Core.Module.TupleDispatch.Element) :=
  (scalarTuple? source).map (List.map .scalar)

def constructorTuple? : Source.Expr → Option (List Core.Module.TupleDispatch.Element)
  | .tuple elements => (elements.mapM tupleScalar?).map (List.map .scalar)
  | _ => none

inductive TupleConstructorArgument :
    List (Source.ArgumentKind × Source.Expr) → Option (List Core.Module.TupleDispatch.Element) → Prop where
  | empty : TupleConstructorArgument [] none
  | exact {source values} (checked : constructorTuple? source = some values) :
      TupleConstructorArgument [(.positional, source)] (some values)

def tupleConstructorArgument? :
    (arguments : List (Source.ArgumentKind × Source.Expr)) →
    Option {argument // TupleConstructorArgument arguments argument}
  | [] => some ⟨none, .empty⟩
  | [(.positional, source)] =>
    match checked : constructorTuple? source with
    | some values => some ⟨some values, .exact checked⟩
    | none => none
  | _ => none

inductive TupleOperandTranslation (scope : Scope) : Source.Expr → TupleOperand scope → Prop where
  | literal {source values} (checked : scalarTupleElements? source = some values) :
      TupleOperandTranslation scope source (.literal values)
  | global (name : String) (reference : GlobalReference scope name) :
      TupleOperandTranslation scope (.name name) (.global name reference)
  | add {left right first second}
      (checkedLeft : scalarTupleElements? left = some first) (checkedRight : scalarTupleElements? right = some second) :
      TupleOperandTranslation scope (.binary .add left right) (.add first second)
  | boundAdd {source receiver argument left right}
      (call : TupleAddCall source receiver [(.positional, argument)])
      (checkedReceiver : scalarTupleElements? receiver = some left) (checkedArgument : scalarTupleElements? argument = some right) :
      TupleOperandTranslation scope source (.boundAdd left right)
  | unboundAdd {source receiver argument left right reference}
      (call : TupleAddCall source (.name "tuple") [(.positional, receiver), (.positional, argument)])
      (checkedReceiver : scalarTupleElements? receiver = some left) (checkedArgument : scalarTupleElements? argument = some right) :
      TupleOperandTranslation scope source (.unboundAdd reference left right)

  | construct {source arguments reference operand}
      (call : TupleConstructorCall source arguments) (checked : TupleConstructorArgument arguments operand) :
      TupleOperandTranslation scope source (.construct reference operand)
  | constructGlobal {source name reference argument}
      (call : TupleConstructorCall source [(.positional, .name name)]) :
      TupleOperandTranslation scope source (.constructGlobal reference name argument)

def tupleValueOperand? (scope : Scope) : (source : Source.Expr) →
    Option {operand // TupleOperandTranslation scope source operand}
  | .name name => (globalReference? scope name).map fun reference => ⟨.global name reference, .global name reference⟩
  | .binary .add left right =>
    match checkedLeft : scalarTupleElements? left, checkedRight : scalarTupleElements? right with
    | some first, some second => some ⟨.add first second, .add checkedLeft checkedRight⟩
    | _, _ => none
  | source =>
    match checked : scalarTupleElements? source with
    | some values => some ⟨.literal values, .literal checked⟩
    | none => none

def tupleOperand? (scope : Scope) (source : Source.Expr) :
    Option {operand // TupleOperandTranslation scope source operand} := do
  if let some ⟨arguments, call⟩ := tupleConstructorCall? source then
    let reference ← globalReference? scope "tuple"
    match arguments, call with
    | [(.positional, .name name)], call =>
      let argument ← globalReference? scope name
      return ⟨.constructGlobal reference name argument, .constructGlobal call⟩
    | arguments, call =>
      let ⟨operand, checked⟩ ← tupleConstructorArgument? arguments
      return ⟨.construct reference operand, .construct call checked⟩
  match tupleAddCall? source with
  | some ⟨(receiver, [(.positional, argument)]), call⟩ =>
    match checkedLeft : scalarTupleElements? receiver, checkedRight : scalarTupleElements? argument with
    | some left, some right => some ⟨.boundAdd left right, .boundAdd call checkedLeft checkedRight⟩
    | _, _ => none
  | some ⟨(.name "tuple", [(.positional, receiver), (.positional, argument)]), call⟩ =>
    let reference ← globalReference? scope "tuple"
    match checkedLeft : scalarTupleElements? receiver, checkedRight : scalarTupleElements? argument with
    | some left, some right => some ⟨.unboundAdd reference left right, .unboundAdd call checkedLeft checkedRight⟩
    | _, _ => none
  | some _ => none
  | none => tupleValueOperand? scope source

inductive TupleLinksTranslation (scope : Scope) :
    List (Source.Comparison × Source.Expr) → List (TupleOperand scope) → Prop where
  | nil : TupleLinksTranslation scope [] []
  | cons {source operand rest tail} (checked : TupleOperandTranslation scope source operand)
      (remaining : TupleLinksTranslation scope rest tail) :
      TupleLinksTranslation scope ((.eq, source) :: rest) (operand :: tail)

def tupleLinks? (scope : Scope) : (links : List (Source.Comparison × Source.Expr)) →
    Option {operands // TupleLinksTranslation scope links operands}
  | [] => some ⟨[], .nil⟩
  | (.eq, source) :: rest => do
    let head ← tupleOperand? scope source
    let tail ← tupleLinks? scope rest
    return ⟨head.val :: tail.val, .cons head.property tail.property⟩
  | _ => none

structure TupleChainTest (scope : Scope) where
  first : TupleOperand scope
  links : List (TupleOperand scope)

inductive TupleChainTranslation (scope : Scope) : Source.Stmt → TupleChainTest scope → Prop where
  | assertion {source link rest first links} (initial : TupleOperandTranslation scope source first)
      (checked : TupleLinksTranslation scope (link :: rest) links)
      (callsTuple : (first :: links).any TupleOperand.usesCall = true) :
      TupleChainTranslation scope (.assert_ (.comparison source (link :: rest)) none) ⟨first, links⟩

def tupleChainTest? (scope : Scope) : (statement : Source.Stmt) →
    Option {test // TupleChainTranslation scope statement test}
  | .assert_ (.comparison source (link :: rest)) none => do
    let first ← tupleOperand? scope source
    let links ← tupleLinks? scope (link :: rest)
    if callsTuple : (first.val :: links.val).any TupleOperand.usesCall then
      some ⟨⟨first.val, links.val⟩, .assertion first.property links.property callsTuple⟩
    else none
  | _ => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
