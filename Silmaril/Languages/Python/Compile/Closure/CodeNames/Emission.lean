module

public import Silmaril.Languages.Python.Compile.Closure.Link.Code

/-! # Name table evidence for checked ordinary function code

This profile models the name operands interned by CPython 3.7.3 and 3.13.5
in `exec` mode with optimization level zero. Each block has its own table.
An assertion failure contributes a name in 3.7.3 and a dedicated opcode in
3.13.5. Local and captured slots contribute no name-table operand.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.CodeNames

open Core.Closure (Layout)
open Source (Name)

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

end Silmaril.Languages.Python.Compile.Closure.CodeNames
