module

public import Silmaril.Languages.Python.Compile.Closure.Link.Defs

/-! # Name table evidence for checked ordinary function code

This profile models the name operands interned by CPython 3.7.3 and 3.13.5
in `exec` mode with optimization level zero. Each block has its own table.
An assertion failure contributes a name in 3.7.3 and a dedicated opcode in
3.13.5. Local and captured slots contribute no name-table operand.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.CodeNames

open Core.Closure (CodeRef Layout)
open Source (Name Scope ScopeTree)

inductive Version where
  | cpython373
  | cpython3135
  deriving DecidableEq, Repr

inductive Operation where
  | globalRead (name : Name)
  | attributeRead (name : Name)
  | assertionFailure
  deriving DecidableEq, Repr

def Operation.name? (version : Version) : Operation → Option Name
  | .globalRead name | .attributeRead name => some name
  | .assertionFailure => if version == .cpython373 then some "AssertionError" else none

/-- First interning determines the name's index, including repeated uses
of the same spelling by different instructions. -/
def names (version : Version) (operations : List Operation) : List Name :=
  (operations.filterMap (Operation.name? version)).eraseDups

def readOperations? {layout : Layout} : Body.Expr layout → Option (List Operation)
  | .read _ => some []
  | .globalName name => if name == "__debug__" then none else some [.globalRead name]
  | _ => none

def valueOperations? {layout : Layout} : Body.Expr layout → Option (List Operation)
  | .integer _ | .none => some []
  | value => readOperations? value

/-- Follow the lowering order of this straight-line block. The caller
certifies its nested definitions independently through their code references. -/
def operations? {layout : Layout} : Link.Code layout → Option (List Operation)
  | .ret value => valueOperations? value
  | .assert (.eqInt receiver _) next => do
    let test ← readOperations? receiver
    return test ++ [.assertionFailure] ++ (← operations? next)
  | .assertCodeNames receiver _ next => do
    let test ← readOperations? receiver
    return test ++ [.attributeRead "__code__", .attributeRead "co_names", .assertionFailure] ++
      (← operations? next)
  | .discardCall callee next => do
    let call ← readOperations? callee
    return call ++ (← operations? next)
  | .assign _ value next => do
    let rhs ← valueOperations? value
    return rhs ++ (← operations? next)
  | .closure _ _ _ _ next => operations? next
  | _ => none

structure Evidence (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) where
  block : Link.Block
  found : blocks[ref.key]? = some block
  layout : block.entry.layout = ref.layout
  scope : Scope
  located : tree.atPath block.path = some scope
  scopeLayout : block.entry.layout = frameLayout scope
  operations : List Operation
  emitted : operations? block.entry.definition.body = some operations

def Evidence.tuple {tree : ScopeTree} {blocks : List Link.Block} {ref : CodeRef}
    (evidence : Evidence tree blocks ref) (version : Version) : List Name :=
  names version evidence.operations

/-- Bind the checked name operands to the same key, layout and ordinary
lexical path as the linked function definition. -/
def checked? (tree : ScopeTree) (blocks : List Link.Block) (ref : CodeRef) :
    Option (Evidence tree blocks ref) := do
  match found : blocks[ref.key]? with
  | none => none
  | some block =>
    if layout : block.entry.layout = ref.layout then
      let ⟨scope, located, scopeLayout⟩ ← Link.blockScope? tree block
      match emitted : operations? block.entry.definition.body with
      | none => none
      | some operations => return ⟨block, found, layout, scope, located, scopeLayout, operations, emitted⟩
    else none

end Silmaril.Languages.Python.Compile.Closure.CodeNames
